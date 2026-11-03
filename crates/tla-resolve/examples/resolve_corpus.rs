//! Resolves the spec of every model (a `.cfg` beside a `.tla` of the same name) under a
//! directory, or every module with `--all`, and summarizes the failures:
//! `cargo run --release -p tla-resolve --example resolve_corpus -- DIR [--all] [--library DIR]...`
//!
//! A module is looked up beside the spec first, then in the library directories. Every failure
//! is also written to stderr as `path<TAB>message`, for scripts.

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::time::Instant;

fn main() {
    let mut args = std::env::args().skip(1);
    let root = PathBuf::from(args.next().expect("usage: resolve_corpus DIR [--library DIR]..."));
    let mut library = HashMap::new();
    let mut is_all = false;
    while let Some(flag) = args.next() {
        if flag == "--all" {
            is_all = true;
            continue;
        }
        assert_eq!(flag, "--library", "unknown argument {flag}");
        let mut files = Vec::new();
        collect(
            &PathBuf::from(args.next().expect("--library needs a directory")),
            "tla",
            &mut files,
        );
        for path in files {
            let name = path.file_stem().unwrap().to_string_lossy().into_owned();
            // TLC finds its standard modules before any library module of the same name.
            if !tla_resolve::is_standard_module(&name) {
                library.entry(name).or_insert(path);
            }
        }
    }
    let mut specs = Vec::new();
    collect(&root, if is_all { "tla" } else { "cfg" }, &mut specs);
    specs.sort();

    let started = Instant::now();
    let mut resolved = 0;
    let mut failures = BTreeMap::<String, Vec<String>>::new();
    for spec in &specs {
        let spec_path = spec.with_extension("tla");
        let Ok(source) = std::fs::read_to_string(&spec_path) else { continue };
        let directory = spec_path.parent().unwrap().to_path_buf();
        let mut loader = |name: &str| {
            let beside = directory.join(format!("{name}.tla"));
            std::fs::read_to_string(&beside)
                .ok()
                .or_else(|| library.get(name).and_then(|path| std::fs::read_to_string(path).ok()))
        };
        // TLC requires the root module to be named after its file.
        let stem = spec_path.file_stem().unwrap().to_string_lossy();
        let result = tla_resolve::resolve(&source, &mut loader).and_then(|spec| {
            let root = spec.modules[0].name;
            if root.as_str() == stem {
                return Ok(spec);
            }
            let message = format!("File name '{stem}' does not match the name '{root}' of the top level module it contains.");
            Err(tla_resolve::ResolveError { message, module: root, span: Default::default(), line: 1, column: 1 })
        });
        match result {
            Ok(_) => resolved += 1,
            Err(error) => {
                eprintln!("{}\t{}", spec_path.display(), error.message.replace('\n', " "));
                let location = format!("{} ({error})", spec_path.display());
                failures.entry(error.message).or_default().push(location);
            }
        }
    }

    let mut grouped: Vec<_> = failures.into_iter().collect();
    grouped.sort_by_key(|(_, locations)| std::cmp::Reverse(locations.len()));
    for (message, locations) in &grouped {
        println!("{:>4}  {}", locations.len(), message.replace('\n', " "));
        for location in locations.iter().take(2) {
            println!("        {location}");
        }
    }
    let total = resolved + grouped.iter().map(|(_, locations)| locations.len()).sum::<usize>();
    println!("{resolved} of {total} specs resolved in {:.2?}", started.elapsed());
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
