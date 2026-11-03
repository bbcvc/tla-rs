//! Prints TLC's string order for every model (a `.cfg` beside a `.tla` of the same name) under a
//! directory, one JSON line per model, to compare with tla-ts's `getTlcStringOrder`, or with
//! `--variables` TLC's order of the variables, to compare with `getTlcVariableOrder`:
//!
//! ```text
//! cargo run --release -p tla-resolve --example string_order -- DIR [--variables] [--library DIR]...
//! ```

use std::collections::HashMap;
use std::path::{Path, PathBuf};

fn collect(path: &Path, extension: &str, files: &mut Vec<PathBuf>) {
    if path.is_dir() {
        for entry in std::fs::read_dir(path).into_iter().flatten().flatten() {
            collect(&entry.path(), extension, files);
        }
    } else if path.extension().is_some_and(|found| found == extension) {
        files.push(path.to_path_buf());
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let root = PathBuf::from(args.next().expect("usage: string_order DIR [--library DIR]..."));
    let mut library = HashMap::new();
    let mut variables = false;
    while let Some(flag) = args.next() {
        if flag == "--variables" {
            variables = true;
            continue;
        }
        assert_eq!(flag, "--library");
        let mut files = Vec::new();
        collect(Path::new(&args.next().expect("a library directory")), "tla", &mut files);
        files.sort();
        for path in files {
            let name = path.file_stem().unwrap().to_string_lossy().into_owned();
            if !tla_resolve::is_standard_module(&name) {
                library.entry(name).or_insert(path);
            }
        }
    }
    let mut configs = Vec::new();
    collect(&root, "cfg", &mut configs);
    configs.sort();
    for config_path in configs {
        let spec_path = config_path.with_extension("tla");
        let Ok(source) = std::fs::read_to_string(&spec_path) else { continue };
        let id = config_path.strip_prefix(&root).unwrap().to_string_lossy().into_owned();
        let config = std::fs::read_to_string(&config_path).unwrap_or_default();
        let Ok(config) = tla_parser::parse_config(&config) else {
            println!("{}", serde_json::json!({ "id": id, "error": "config" }));
            continue;
        };
        let directory = spec_path.parent().unwrap().to_path_buf();
        let mut loader = |name: &str| {
            std::fs::read_to_string(directory.join(format!("{name}.tla")))
                .ok()
                .or_else(|| library.get(name).and_then(|path| std::fs::read_to_string(path).ok()))
        };
        let order = match variables {
            true => tla_resolve::tlc_variable_order(&source, &mut loader),
            false => tla_resolve::tlc_string_order(&source, &config, &mut loader),
        };
        let line = match order {
            Ok(order) => serde_json::json!({ "id": id, "order": order }),
            Err(error) => serde_json::json!({ "id": id, "error": error }),
        };
        println!("{line}");
    }
}
