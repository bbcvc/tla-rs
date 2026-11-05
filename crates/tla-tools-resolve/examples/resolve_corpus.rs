//! Resolves the spec of every model (a `.cfg` beside a `.tla` of the same name) under a
//! directory, or every module with `--all`, and summarizes the failures:
//!
//! ```text
//! cargo run --release -p tla-tools-resolve --example resolve_corpus -- DIR [--all] [--library DIR]...
//!     [--sany sany.json] [--expected expected.json]
//! ```
//!
//! A module is looked up beside the spec first, then in the library directories. Every failure
//! is also written to stderr as `path<TAB>message`, for scripts.
//!
//! With tla-ts's conformance records, ids relative to `DIR`, it also compares the results:
//! `--sany` against SANY's verdict on each module, and `--expected` against TLC's result for
//! each model, where only a model TLC reports as an error should fail to resolve.

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::time::Instant;

use tla_tools_resolve::ResolveError;

struct Options {
    root: PathBuf,
    is_all: bool,
    library: HashMap<String, PathBuf>,
    sany: Option<PathBuf>,
    expected: Option<PathBuf>,
}

fn options() -> Options {
    let mut args = std::env::args().skip(1);
    let usage =
        "usage: resolve_corpus DIR [--all] [--library DIR]... [--sany FILE] [--expected FILE]";
    let mut options = Options {
        root: PathBuf::from(args.next().expect(usage)),
        is_all: false,
        library: HashMap::new(),
        sany: None,
        expected: None,
    };
    while let Some(flag) = args.next() {
        let mut value = || PathBuf::from(args.next().expect(usage));
        match flag.as_str() {
            "--all" => options.is_all = true,
            "--sany" => options.sany = Some(value()),
            "--expected" => options.expected = Some(value()),
            "--library" => {
                let mut files = Vec::new();
                collect(&value(), "tla", &mut files);
                for path in files {
                    let name = path.file_stem().unwrap().to_string_lossy().into_owned();
                    // TLC finds its standard modules before any library module of the same name.
                    if !tla_tools_resolve::is_standard_module(&name) {
                        options.library.entry(name).or_insert(path);
                    }
                }
            }
            _ => panic!("{usage}"),
        }
    }
    options
}

fn resolve(spec_path: &Path, library: &HashMap<String, PathBuf>) -> Result<(), ResolveError> {
    let source = std::fs::read_to_string(spec_path).unwrap_or_default();
    let directory = spec_path.parent().unwrap().to_path_buf();
    let mut loader = |name: &str| {
        std::fs::read_to_string(directory.join(format!("{name}.tla")))
            .ok()
            .or_else(|| library.get(name).and_then(|path| std::fs::read_to_string(path).ok()))
    };
    let spec = tla_tools_resolve::resolve(&source, &mut loader)?;
    // TLC requires the root module to be named after its file.
    let stem = spec_path.file_stem().unwrap().to_string_lossy();
    let root = spec.modules[0].name;
    if root.as_str() == stem {
        return Ok(());
    }
    let message = format!(
        "File name '{stem}' does not match the name '{root}' of the top level module it contains."
    );
    Err(ResolveError { message, module: root, span: Default::default(), line: 1, column: 1 })
}

fn main() {
    let options = options();
    let mut specs = Vec::new();
    collect(&options.root, if options.is_all { "tla" } else { "cfg" }, &mut specs);
    specs.sort();

    let started = Instant::now();
    let mut results = BTreeMap::<String, Option<String>>::new();
    let mut failures = BTreeMap::<String, Vec<String>>::new();
    for spec in &specs {
        let spec_path = spec.with_extension("tla");
        if !spec_path.exists() {
            continue;
        }
        let id = spec.strip_prefix(&options.root).unwrap().to_string_lossy().into_owned();
        let failure = resolve(&spec_path, &options.library).err();
        if let Some(error) = &failure {
            eprintln!("{}\t{}", spec_path.display(), error.message.replace('\n', " "));
            let location = format!("{} ({error})", spec_path.display());
            failures.entry(error.message.clone()).or_default().push(location);
        }
        results.insert(id, failure.map(|error| error.message));
    }

    let mut grouped: Vec<_> = failures.into_iter().collect();
    grouped.sort_by_key(|(_, locations)| std::cmp::Reverse(locations.len()));
    for (message, locations) in &grouped {
        println!("{:>4}  {}", locations.len(), message.replace('\n', " "));
        for location in locations.iter().take(2) {
            println!("        {location}");
        }
    }
    let resolved = results.values().filter(|failure| failure.is_none()).count();
    println!("{resolved} of {} specs resolved in {:.2?}", results.len(), started.elapsed());

    if let Some(path) = &options.sany {
        compare_with_sany(path, &results);
    }
    if let Some(path) = &options.expected {
        compare_with_tlc(path, &results);
    }
}

fn records(path: &Path) -> Vec<serde_json::Value> {
    let text = std::fs::read_to_string(path).expect("read the records");
    serde_json::from_str(&text).expect("the records are a JSON array")
}

/// The first line of a SANY error that says what is wrong, rather than where.
fn reason(error: &str) -> &str {
    let skipped = ["***", "line ", "In module", "Semantic", "Fatal", "Unknown location"];
    error
        .lines()
        .find(|line| {
            !line.trim().is_empty() && !skipped.iter().any(|prefix| line.starts_with(prefix))
        })
        .unwrap_or(error)
}

fn compare_with_sany(path: &Path, results: &BTreeMap<String, Option<String>>) {
    let mut agreed = 0;
    let mut compared = 0;
    let mut mismatches = Vec::new();
    for record in records(path) {
        let id = record["id"].as_str().unwrap();
        let Some(failure) = results.get(id) else { continue };
        compared += 1;
        match (record["status"] == "ok", failure) {
            (true, None) | (false, Some(_)) => agreed += 1,
            (true, Some(message)) => mismatches.push(format!("rejects {id}: {message}")),
            (false, None) => {
                let error = record["error"].as_str().unwrap_or_default();
                mismatches.push(format!("accepts {id}: SANY says {}", reason(error)));
            }
        }
    }
    println!("\nAgrees with SANY on {agreed} of {compared} modules");
    mismatches.iter().for_each(|mismatch| println!("  {mismatch}"));
}

fn compare_with_tlc(path: &Path, results: &BTreeMap<String, Option<String>>) {
    let mut rejected = Vec::new();
    for record in records(path) {
        let id = record["id"].as_str().unwrap();
        if let (Some(Some(message)), false) = (results.get(id), record["status"] == "error") {
            rejected.push(format!("{id} ({}): {message}", record["status"].as_str().unwrap()));
        }
    }
    println!("\nRejects {} models that TLC checks", rejected.len());
    rejected.iter().for_each(|model| println!("  {model}"));
}

fn collect(path: &Path, extension: &str, files: &mut Vec<PathBuf>) {
    if path.is_dir() {
        for entry in std::fs::read_dir(path).into_iter().flatten().flatten() {
            collect(&entry.path(), extension, files);
        }
    } else if path.extension().is_some_and(|found| found == extension) {
        files.push(path.to_path_buf());
    }
}
