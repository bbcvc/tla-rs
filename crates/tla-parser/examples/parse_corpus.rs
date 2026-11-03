//! Parses every `.tla` and `.cfg` file under the given directories and summarizes the failures:
//! `cargo run --release -p tla-parser --example parse_corpus -- DIR...`

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

fn main() {
    let roots: Vec<PathBuf> = std::env::args().skip(1).map(PathBuf::from).collect();
    assert!(!roots.is_empty(), "usage: parse_corpus DIR...");
    let mut files = Vec::new();
    for root in &roots {
        collect(root, &mut files);
    }
    files.sort();

    let started = Instant::now();
    let mut counts = BTreeMap::<&str, (usize, usize)>::new();
    let mut failures = BTreeMap::<String, Vec<String>>::new();
    for path in &files {
        let Ok(source) = std::fs::read_to_string(path) else { continue };
        let extension = path.extension().and_then(|extension| extension.to_str()).unwrap_or("");
        let failure = match extension {
            "tla" => tla_parser::parse_module(&source).err().map(|error| {
                (error.message, format!("{}:{}:{}", path.display(), error.line, error.column))
            }),
            _ => tla_parser::parse_config(&source)
                .err()
                .map(|error| (error.message.replace('\n', " "), path.display().to_string())),
        };
        let count = counts.entry(if extension == "tla" { "tla" } else { "cfg" }).or_default();
        count.0 += 1;
        if let Some((message, location)) = failure {
            count.1 += 1;
            failures.entry(message).or_default().push(location);
        }
    }

    let mut grouped: Vec<_> = failures.into_iter().collect();
    grouped.sort_by_key(|(_, locations)| std::cmp::Reverse(locations.len()));
    for (message, locations) in &grouped {
        println!("{:>4}  {message}", locations.len());
        for location in locations.iter().take(3) {
            println!("        {location}");
        }
    }
    for (kind, (total, failed)) in counts {
        println!("{kind}: {} of {total} parsed", total - failed);
    }
    println!("{:.2?}", started.elapsed());
}

fn collect(path: &Path, files: &mut Vec<PathBuf>) {
    if path.is_dir() {
        for entry in std::fs::read_dir(path).into_iter().flatten().flatten() {
            collect(&entry.path(), files);
        }
    } else if matches!(
        path.extension().and_then(|extension| extension.to_str()),
        Some("tla" | "cfg")
    ) {
        files.push(path.to_path_buf());
    }
}
