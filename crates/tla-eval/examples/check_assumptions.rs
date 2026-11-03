//! Checks the `ASSUME`s of every model (a `.cfg` beside a `.tla` of the same name) under a
//! directory, as TLC does before it explores any state, and compares the outcome with TLC's
//! recorded results:
//!
//! ```text
//! cargo run --release -p tla-eval --example check_assumptions -- DIR [--library DIR]...
//!     [--expected expected.json] [--timeout SECONDS] [--jobs N] [--outcomes FILE]
//! ```
//!
//! A model TLC records as an `assumption-violation` should violate an assumption here, and a
//! model TLC checks without an error should satisfy all of them. As in TLC, an assumption that
//! fails to evaluate is violated. Each model is checked in a
//! child process, so a model that runs too long or overflows the stack only fails itself.

use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use tla_eval::{CheckerOptions, Evaluator, bind_model};

const USAGE: &str = "usage: check_assumptions DIR [--library DIR]... [--expected FILE] \
                     [--timeout SECONDS] [--jobs N] [--outcomes FILE]";

enum Outcome {
    Satisfied,
    /// The assumptions hold, but TLC reports a violated postcondition as a violated assumption,
    /// and checking postconditions needs the model checker.
    Postconditions,
    Violated(String),
    Error(String),
    Timeout,
}

impl fmt::Display for Outcome {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Outcome::Satisfied => write!(formatter, "satisfied"),
            Outcome::Postconditions => write!(formatter, "satisfied, with postconditions"),
            Outcome::Violated(message) => write!(formatter, "violated: {message}"),
            Outcome::Error(message) => write!(formatter, "error: {message}"),
            Outcome::Timeout => write!(formatter, "timeout"),
        }
    }
}

impl Outcome {
    /// The line a child process prints.
    fn encode(&self) -> String {
        let escape = |message: &str| message.replace('\\', "\\\\").replace('\n', "\\n");
        match self {
            Outcome::Satisfied => "satisfied".into(),
            Outcome::Postconditions => "postconditions".into(),
            Outcome::Violated(message) => format!("violated\t{}", escape(message)),
            Outcome::Error(message) => format!("error\t{}", escape(message)),
            Outcome::Timeout => "timeout".into(),
        }
    }

    fn decode(line: &str) -> Option<Outcome> {
        let (kind, message) = line.split_once('\t').unwrap_or((line, ""));
        let message = message.replace("\\n", "\n").replace("\\\\", "\\");
        Some(match kind {
            "satisfied" => Outcome::Satisfied,
            "postconditions" => Outcome::Postconditions,
            "violated" => Outcome::Violated(message),
            "error" => Outcome::Error(message),
            "timeout" => Outcome::Timeout,
            _ => return None,
        })
    }
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
    let has_postconditions = !config.postconditions.is_empty() || !config.possible.is_empty();
    let assumptions = spec.assumptions.clone();
    let evaluator = Evaluator::new(Arc::new(spec), model.constants).with_overrides(model.overrides);
    // TLC creates its model checker, whose options TLCGet("config") reads, before it checks the
    // assumptions. The options TLC takes from its command line keep their defaults.
    evaluator.runtime().start(CheckerOptions::for_config(&config));
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
            // TLC reports an assumption it fails to evaluate as violated.
            Ok(value) => return Outcome::Violated(format!("assumption evaluated to {value}")),
            Err(error) => return Outcome::Violated(error.to_string()),
        }
    }
    if has_postconditions { Outcome::Postconditions } else { Outcome::Satisfied }
}

/// Checks one model in this process, on a thread with a large stack, and prints the outcome.
fn check_one(spec_path: PathBuf, library: HashMap<String, PathBuf>) {
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || check(&spec_path, &library))
        .unwrap()
        .join()
        .unwrap_or_else(|panic| {
            let message = panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| panic.downcast_ref::<&str>().map(|text| text.to_string()))
                .unwrap_or_default();
            Outcome::Error(format!("panic: {message}"))
        });
    println!("{}", outcome.encode());
}

/// Checks one model in a child process, killing it after `timeout`.
fn check_in_child(spec_path: &Path, library_args: &[String], timeout: Duration) -> Outcome {
    let mut child = Command::new(std::env::current_exe().unwrap())
        .arg("--one")
        .arg(spec_path)
        .args(library_args)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("the checker can run itself");
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if started.elapsed() > timeout {
            let _ = child.kill();
            let _ = child.wait();
            return Outcome::Timeout;
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    let mut output = String::new();
    let _ = child.stdout.take().unwrap().read_to_string(&mut output);
    output
        .lines()
        .last()
        .and_then(Outcome::decode)
        .unwrap_or_else(|| Outcome::Error(format!("the checker crashed: {status}")))
}

fn main() {
    let mut args = std::env::args().skip(1);
    let first = args.next().expect(USAGE);
    let (root, is_one) = match first.as_str() {
        "--one" => (PathBuf::from(args.next().expect(USAGE)), true),
        _ => (PathBuf::from(first), false),
    };
    let mut library = HashMap::new();
    let mut library_args = Vec::new();
    let mut expected = None;
    let mut outcomes_path = None;
    let mut timeout = Duration::from_secs(10);
    let mut jobs = std::thread::available_parallelism().map_or(4, |count| count.get());
    while let Some(flag) = args.next() {
        let value = args.next().expect(USAGE);
        match flag.as_str() {
            "--expected" => expected = Some(PathBuf::from(value)),
            "--outcomes" => outcomes_path = Some(PathBuf::from(value)),
            "--timeout" => timeout = Duration::from_secs_f64(value.parse().expect(USAGE)),
            "--jobs" => jobs = value.parse().expect(USAGE),
            "--library" => {
                let mut files = Vec::new();
                collect(Path::new(&value), "tla", &mut files);
                for path in files {
                    let name = path.file_stem().unwrap().to_string_lossy().into_owned();
                    if !tla_resolve::is_standard_module(&name) {
                        library.entry(name).or_insert(path);
                    }
                }
                library_args.extend(["--library".to_string(), value]);
            }
            _ => panic!("{USAGE}"),
        }
    }
    if is_one {
        return check_one(root, library);
    }

    let mut configs = Vec::new();
    collect(&root, "cfg", &mut configs);
    configs.sort();
    let pending: Vec<(String, PathBuf)> = configs
        .iter()
        .map(|config| config.with_extension("tla"))
        .filter(|spec_path| spec_path.exists())
        .map(|spec_path| {
            let id = spec_path.with_extension("cfg");
            (id.strip_prefix(&root).unwrap().to_string_lossy().into_owned(), spec_path)
        })
        .collect();

    let started = Instant::now();
    let queue = Mutex::new(pending.into_iter());
    let outcomes = Mutex::new(BTreeMap::new());
    std::thread::scope(|scope| {
        for _ in 0..jobs {
            scope.spawn(|| {
                loop {
                    let Some((id, spec_path)) = queue.lock().unwrap().next() else { break };
                    let outcome = check_in_child(&spec_path, &library_args, timeout);
                    outcomes.lock().unwrap().insert(id, outcome);
                }
            });
        }
    });
    let outcomes = outcomes.into_inner().unwrap();
    let count = |predicate: fn(&Outcome) -> bool| {
        outcomes.values().filter(|outcome| predicate(outcome)).count()
    };
    println!(
        "{} models: {} satisfied, {} violated, {} errors, {} timeouts in {:.2?}",
        outcomes.len(),
        count(|outcome| matches!(outcome, Outcome::Satisfied | Outcome::Postconditions)),
        count(|outcome| matches!(outcome, Outcome::Violated(_))),
        count(|outcome| matches!(outcome, Outcome::Error(_))),
        count(|outcome| matches!(outcome, Outcome::Timeout)),
        started.elapsed()
    );

    if let Some(path) = outcomes_path {
        let lines: String =
            outcomes.iter().map(|(id, outcome)| format!("{id}\t{}\n", outcome.encode())).collect();
        std::fs::write(path, lines).unwrap();
    }

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
            ("assumption-violation", Outcome::Violated(_) | Outcome::Postconditions) => false,
            ("assumption-violation", _) => true,
            ("error", _) => false,
            (_, Outcome::Satisfied | Outcome::Postconditions) => false,
            _ => true,
        };
        if is_mismatch {
            mismatches.push(format!("{id} (TLC: {status}): {outcome}"));
        }
    }
    for (id, outcome) in &outcomes {
        if matches!(outcome, Outcome::Timeout) {
            println!("timeout: {id}");
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
