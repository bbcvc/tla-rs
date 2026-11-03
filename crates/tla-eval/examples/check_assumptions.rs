//! Checks the `ASSUME`s of every model (a `.cfg` beside a `.tla` of the same name) under a
//! directory, as TLC does before it explores any state, and compares the outcome with TLC's
//! recorded results:
//!
//! ```text
//! cargo run --release -p tla-eval --example check_assumptions -- DIR [--library DIR]...
//!     [--expected expected.json]
//! ```
//!
//! A model TLC records as an `assumption-violation` should violate an assumption here, and a
//! model TLC checks without an error should satisfy all of them.

use std::collections::{BTreeMap, HashMap};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

use tla_eval::{Evaluator, bind_model};

#[derive(Debug)]
enum Outcome {
    Satisfied,
    Violated(String),
    Error(String),
}

fn check(spec_path: &Path, library: &HashMap<String, PathBuf>) -> Outcome {
    let config = std::fs::read_to_string(spec_path.with_extension("cfg")).unwrap_or_default();
    // TLC interns the configuration's values first, which orders its strings and model values.
    let config = match tla_parser::parse_config(&config) {
        Ok(config) => config,
        Err(error) => return Outcome::Error(error.message),
    };
    let source = std::fs::read_to_string(spec_path).unwrap_or_default();
    let directory = spec_path.parent().unwrap().to_path_buf();
    let mut loader = |name: &str| {
        std::fs::read_to_string(directory.join(format!("{name}.tla")))
            .ok()
            .or_else(|| library.get(name).and_then(|path| std::fs::read_to_string(path).ok()))
    };
    let spec = match tla_resolve::resolve(&source, &mut loader) {
        Ok(spec) => spec,
        Err(error) => return Outcome::Error(error.to_string()),
    };
    let model = match bind_model(&spec, &config) {
        Ok(model) => model,
        Err(error) => return Outcome::Error(error.message),
    };
    let assumptions = spec.assumptions.clone();
    let evaluator = Evaluator::new(Arc::new(spec), model.constants).with_overrides(model.overrides);
    for def in assumptions {
        match evaluator.eval_def(def, None) {
            Ok(value) if value.as_bool() == Some(true) => {}
            Ok(value) if value.as_bool() == Some(false) => {
                let def = evaluator.spec().def(def);
                let module = evaluator.spec().modules[def.module.index()].name;
                return Outcome::Violated(format!(
                    "assumption {} of module {module} is false",
                    def.name
                ));
            }
            Ok(value) => return Outcome::Error(format!("assumption evaluated to {value}")),
            Err(error) => return Outcome::Error(error.to_string()),
        }
    }
    Outcome::Satisfied
}

fn main() {
    let mut args = std::env::args().skip(1);
    let usage = "usage: check_assumptions DIR [--library DIR]... [--expected FILE]";
    let root = PathBuf::from(args.next().expect(usage));
    let mut library = HashMap::new();
    let mut expected = None;
    while let Some(flag) = args.next() {
        let value = PathBuf::from(args.next().expect(usage));
        match flag.as_str() {
            "--expected" => expected = Some(value),
            "--library" => {
                let mut files = Vec::new();
                collect(&value, "tla", &mut files);
                for path in files {
                    let name = path.file_stem().unwrap().to_string_lossy().into_owned();
                    if !tla_resolve::is_standard_module(&name) {
                        library.entry(name).or_insert(path);
                    }
                }
            }
            _ => panic!("{usage}"),
        }
    }
    let mut configs = Vec::new();
    collect(&root, "cfg", &mut configs);
    configs.sort();

    let started = Instant::now();
    std::panic::set_hook(Box::new(|_| {}));
    let mut outcomes = BTreeMap::new();
    for config in &configs {
        let spec_path = config.with_extension("tla");
        if !spec_path.exists() {
            continue;
        }
        let id = config.strip_prefix(&root).unwrap().to_string_lossy().into_owned();
        let outcome = catch_unwind(AssertUnwindSafe(|| check(&spec_path, &library)))
            .unwrap_or_else(|panic| {
                let message = panic
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| panic.downcast_ref::<&str>().map(|text| text.to_string()))
                    .unwrap_or_default();
                Outcome::Error(format!("panic: {message}"))
            });
        outcomes.insert(id, outcome);
    }
    let count = |predicate: fn(&Outcome) -> bool| {
        outcomes.values().filter(|outcome| predicate(outcome)).count()
    };
    println!(
        "{} models: {} satisfied, {} violated, {} errors in {:.2?}",
        outcomes.len(),
        count(|outcome| matches!(outcome, Outcome::Satisfied)),
        count(|outcome| matches!(outcome, Outcome::Violated(_))),
        count(|outcome| matches!(outcome, Outcome::Error(_))),
        started.elapsed()
    );

    let Some(expected) = expected else { return };
    let records: Vec<serde_json::Value> =
        serde_json::from_str(&std::fs::read_to_string(expected).unwrap()).unwrap();
    let mut mismatches = Vec::new();
    for record in records {
        let (Some(id), Some(status)) = (record["id"].as_str(), record["status"].as_str()) else {
            continue;
        };
        let Some(outcome) = outcomes.get(id) else { continue };
        let is_mismatch = match (status, outcome) {
            ("assumption-violation", Outcome::Violated(_)) => false,
            ("assumption-violation", _) => true,
            ("error", _) => false,
            (_, Outcome::Satisfied) => false,
            _ => true,
        };
        if is_mismatch {
            mismatches.push(format!("{id} (TLC: {status}): {outcome:?}"));
        }
    }
    println!("\n{} models disagree with TLC", mismatches.len());
    mismatches.iter().for_each(|mismatch| println!("  {}", mismatch.replace('\n', " ")));
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
