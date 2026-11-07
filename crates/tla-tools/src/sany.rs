//! What SANY prints as TLC runs it on a spec: the file it parses each module from, each module it
//! analyzes and lints, and why it rejects the spec.
//!
//! tla-rs parses with tree-sitter rather than SANY's parser, so a syntax error is reported at
//! tree-sitter's position in tree-sitter's words, inside SANY's report of it.

use std::fmt::Write;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use tla_tools_checker::load::{ErrorKind, Modules, ParseFailure, ResolveError, is_standard_module};

/// The standard modules SANY doesn't lint (`tla2sany.semantic.StandardModules`).
const UNLINTED_MODULES: &[&str] = &[
    "FiniteSets",
    "Sequences",
    "Bags",
    "Naturals",
    "Integers",
    "Reals",
    "RealTime",
    "Randomization",
    "TLC",
];

/// Where TLC says it reads each module from.
struct Files<'a> {
    modules: &'a Modules,
    spec_path: &'a Path,
    /// The directory TLC copies its standard modules into, a new one for each run.
    library: PathBuf,
}

impl<'a> Files<'a> {
    fn new(modules: &'a Modules, spec_path: &'a Path) -> Self {
        let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |time| time.as_nanos());
        let name = format!("tlc-{}", (nanos as u64 ^ u64::from(std::process::id())) >> 1);
        Self { modules, spec_path, library: temporary_directory().join(name) }
    }

    /// The file a module is parsed from: its own file, a copy of a standard module in TLC's
    /// temporary directory, or for a module that follows the root module in its file, a copy
    /// of it followed by the root module's file.
    fn path(&self, name: &str) -> String {
        if let Some((_, path)) = self.modules.files.iter().find(|(known, _)| known == name) {
            return canonical(path).display().to_string();
        }
        if is_standard_module(name) {
            return self.library.join(format!("{name}.tla")).display().to_string();
        }
        let copy = self.library.join(name).join(format!("{name}.tla"));
        format!("{} ({})", copy.display(), canonical(self.spec_path).display())
    }

    fn parsed(&self, names: &[String], out: &mut String) {
        for name in names {
            let _ = writeln!(out, "Parsing file {}", self.path(name));
        }
    }
}

fn temporary_directory() -> PathBuf {
    let directory = std::env::temp_dir();
    canonical(&directory)
}

fn canonical(path: &Path) -> PathBuf {
    std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

/// What SANY prints for a spec it accepts.
pub fn accepted(modules: &Modules, spec_path: &Path) -> String {
    let mut out = String::new();
    Files::new(modules, spec_path).parsed(&modules.order.parsed, &mut out);
    for name in &modules.order.analyzed {
        let _ = writeln!(out, "Semantic processing of module {name}");
    }
    for name in &modules.order.analyzed {
        if !UNLINTED_MODULES.contains(&name.as_str()) {
            let _ = writeln!(out, "Linting of module {name}");
        }
    }
    out
}

/// What SANY prints for a spec it rejects, where `spec_name` is the name TLC gives SANY.
pub fn rejected(failure: &ParseFailure, spec_path: &Path, spec_name: &str) -> String {
    let mut out = String::new();
    let modules = &failure.modules;
    let files = Files::new(modules, spec_path);
    let Some(error) = &failure.error else {
        files.parsed(&modules.order.parsed, &mut out);
        let _ = writeln!(out, "{}\n", failure.message);
        return out;
    };
    match error.kind {
        ErrorKind::Syntax => {
            let module = match error.module.as_str() {
                "" => spec_name.to_owned(),
                name => name.to_owned(),
            };
            let parsed = &modules.order.parsed;
            let end =
                parsed.iter().position(|name| *name == module).map_or(parsed.len(), |at| at + 1);
            files.parsed(&parsed[..end], &mut out);
            let _ = writeln!(
                out,
                "***Parse Error***\n{} at line {}, column {}\n",
                error.message, error.line, error.column
            );
            let message = format!("Could not parse module {module} from file {module}.tla");
            fatal(spec_name, &module, &message, &mut out);
        }
        ErrorKind::Fatal => {
            files.parsed(&modules.order.parsed, &mut out);
            // SANY names the module that imports the one it can't find.
            let (module, message) = match &modules.order.error {
                Some(message) => {
                    let importer =
                        message.rsplit_once(" imported in module ").map(|(_, rest)| rest);
                    let importer = importer.map(|rest| rest.trim_end_matches('.').to_owned());
                    (importer.unwrap_or_else(|| error.module.to_string()), message.clone())
                }
                None => (error.module.to_string(), error.message.clone()),
            };
            fatal(spec_name, &module, &message, &mut out);
        }
        ErrorKind::Semantic => {
            files.parsed(&modules.order.parsed, &mut out);
            semantic_error(&modules.order.analyzed, error, &mut out);
        }
    }
    out
}

/// SANY's report of a fatal error in `module`: it stops reading the spec.
fn fatal(spec_name: &str, module: &str, message: &str, out: &mut String) {
    let details = format!("In module {module}\n\n{message}");
    let _ = writeln!(out, "\nFatal errors while parsing TLA+ spec in file {spec_name}\n");
    let _ = writeln!(out, "{details}");
    let _ = writeln!(out, "*** Errors: 1\n\n{details}\n\n\n");
}

/// SANY's report of a semantic error: it goes on analyzing the modules after the one with the
/// error, and prints the errors so far after each.
fn semantic_error(analyzed: &[String], error: &ResolveError, out: &mut String) {
    let location = format!(
        "line {}, col {} to line {}, col {} of module {}",
        error.line, error.column, error.end_line, error.end_column, error.module
    );
    let report =
        format!("Semantic errors:\n\n*** Errors: 1\n\n{location}\n\n{}\n\n", error.message);
    let start = analyzed.iter().position(|name| name == error.module.as_str());
    for (index, name) in analyzed.iter().enumerate() {
        let _ = writeln!(out, "Semantic processing of module {name}");
        if start.is_some_and(|start| index >= start) {
            let _ = writeln!(out, "{report}");
        }
    }
    if start.is_none() {
        let _ = writeln!(out, "{report}");
    }
}

#[cfg(test)]
mod tests {
    use tla_tools_checker::load::SanyModuleOrder;

    use super::*;

    fn modules(parsed: &[&str], analyzed: &[&str]) -> Modules {
        let names = |names: &[&str]| names.iter().map(|name| name.to_string()).collect();
        let order =
            SanyModuleOrder { parsed: names(parsed), analyzed: names(analyzed), error: None };
        Modules { order, files: Vec::new() }
    }

    #[test]
    fn lints_the_modules_other_than_the_standard_ones_sany_exempts() {
        let modules = modules(&["R", "Naturals", "TLCExt"], &["Naturals", "TLCExt", "R"]);
        let text = accepted(&modules, Path::new("R.tla"));
        let lines: Vec<&str> = text.lines().filter(|line| !line.starts_with("Parsing")).collect();
        assert_eq!(
            lines,
            [
                "Semantic processing of module Naturals",
                "Semantic processing of module TLCExt",
                "Semantic processing of module R",
                "Linting of module TLCExt",
                "Linting of module R",
            ]
        );
    }

    #[test]
    fn repeats_a_semantic_error_after_each_module_analyzed_after_it() {
        let error = ResolveError {
            message: "Unknown operator: `z'.".to_owned(),
            module: tla_tools_eval::value::Symbol::intern("M"),
            span: Default::default(),
            line: 3,
            column: 6,
            end_line: 3,
            end_column: 6,
            kind: ErrorKind::Semantic,
        };
        let mut out = String::new();
        semantic_error(&["Naturals".into(), "M".into(), "R".into()], &error, &mut out);
        let report = "Semantic errors:\n\n*** Errors: 1\n\nline 3, col 6 to line 3, col 6 of module M\n\nUnknown operator: `z'.\n\n\n";
        let expected = format!(
            "Semantic processing of module Naturals\nSemantic processing of module M\n{report}Semantic processing of module R\n{report}"
        );
        assert_eq!(out, expected);
    }
}
