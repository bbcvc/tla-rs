//! Checks every model TLC was recorded on and compares the outcome with TLC's, as tla-ts's
//! `scripts/conformance.ts` does:
//!
//! ```text
//! cargo run --release -p tla-checker --example conformance -- DIR --expected expected.json
//!     [--library DIR]... [--timeout SECONDS] [--jobs N] [--filter TEXT] [--outcomes FILE]
//! ```
//!
//! `DIR` holds the corpora, and each record of `expected.json` names a model by the path of its
//! configuration relative to it. Each model is checked in a child process in its configuration's
//! directory, as TLC ran there, with TLC's `-seed 4`, so a model that runs too long or crashes
//! only fails itself.
//!
//! The comparison follows `compareOutcome`: an error matches an error, and otherwise the status
//! must agree, then the violated invariant or property, the states generated, the distinct
//! states, the depth, and the length of the trace, where TLC's record has them. Liveness isn't
//! checked yet, so a model whose safety part holds where TLC found a liveness violation is
//! unsupported, and one TLC checked successfully is compared on its counts, which liveness
//! checking doesn't change.

use std::collections::{BTreeMap, HashMap};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use tla_checker::{Options, Outcome, Status};

const USAGE: &str = "usage: conformance DIR --expected FILE [--library DIR]... [--timeout SECONDS] \
                     [--jobs N] [--filter TEXT] [--outcomes FILE]";

/// TLC's `-seed` in tla-ts's recordings.
const TLC_SEED: i64 = 4;

/// The fields of an outcome a child process reports, one per line.
#[derive(Clone, Debug, Default)]
struct Reported {
    status: String,
    violation: Option<String>,
    trace_length: Option<u64>,
    generated: Option<u64>,
    distinct: Option<u64>,
    depth: Option<u64>,
    message: Option<String>,
    has_liveness: bool,
}

/// The text `Reported::encode` escaped.
fn unescape(text: &str) -> String {
    let mut unescaped = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(char) = chars.next() {
        unescaped.push(match (char, char == '\\') {
            (_, true) => match chars.next() {
                Some('n') => '\n',
                Some('t') => '\t',
                Some(other) => other,
                None => '\\',
            },
            (char, false) => char,
        });
    }
    unescaped
}

impl Reported {
    fn from_outcome(outcome: &Outcome) -> Self {
        Self {
            status: outcome.status.name().to_owned(),
            violation: outcome.violation.clone(),
            trace_length: outcome.trace_length.map(|length| length as u64),
            generated: outcome.generated,
            distinct: outcome.distinct,
            depth: outcome.depth,
            message: outcome.message.clone(),
            has_liveness: outcome.has_liveness,
        }
    }

    fn encode(&self) -> String {
        let escape =
            |text: &str| text.replace('\\', "\\\\").replace('\n', "\\n").replace('\t', "\\t");
        let number = |value: Option<u64>| value.map_or(String::new(), |value| value.to_string());
        [
            self.status.clone(),
            self.violation.as_deref().map(escape).unwrap_or_default(),
            number(self.trace_length),
            number(self.generated),
            number(self.distinct),
            number(self.depth),
            self.message.as_deref().map(escape).unwrap_or_default(),
            if self.has_liveness { "liveness".into() } else { String::new() },
        ]
        .join("\t")
    }

    fn decode(line: &str) -> Option<Self> {
        let fields: Vec<&str> = line.split('\t').collect();
        if fields.len() != 8 {
            return None;
        }
        let unescape = |text: &str| (!text.is_empty()).then(|| unescape(text));
        let number = |text: &str| text.parse().ok();
        Some(Self {
            status: fields[0].to_owned(),
            violation: unescape(fields[1]),
            trace_length: number(fields[2]),
            generated: number(fields[3]),
            distinct: number(fields[4]),
            depth: number(fields[5]),
            message: unescape(fields[6]),
            has_liveness: fields[7] == "liveness",
        })
    }
}

/// Checks one model in this process, on a thread with a large stack.
fn check(spec_path: &Path, config_path: &Path, library: &HashMap<String, PathBuf>) -> Outcome {
    let config = std::fs::read_to_string(config_path).unwrap_or_default();
    // TLC reads the configuration first, which orders its strings and model values.
    let config = match tla_parser::parse_config(&config) {
        Ok(config) => config,
        Err(error) => return Outcome::error(error.message),
    };
    let source = std::fs::read_to_string(spec_path).unwrap_or_default();
    let directory = spec_path.parent().unwrap().to_path_buf();
    let mut loader = |name: &str| {
        std::fs::read_to_string(directory.join(format!("{name}.tla")))
            .ok()
            .or_else(|| library.get(name).and_then(|path| std::fs::read_to_string(path).ok()))
    };
    // TLC orders strings by when it interns them, which every sorted set and record built from
    // here on depends on. The order is the process's, so each model runs in a process of its own.
    if let Ok(order) = tla_resolve::tlc_string_order(&source, &config, &mut loader) {
        tla_eval::value::set_order(order.iter().map(String::as_str));
    }
    let spec = match tla_resolve::resolve(&source, &mut loader) {
        Ok(spec) => spec,
        Err(error) => return Outcome::error(error.to_string()),
    };
    // TLC requires the root module to be named after its file.
    let stem = spec_path.file_stem().unwrap().to_string_lossy();
    if spec.modules[0].name.as_str() != stem {
        return Outcome::error(format!(
            "File name '{stem}' does not match the name '{}' of the top level module it contains.",
            spec.modules[0].name
        ));
    }
    let options = Options { seed: TLC_SEED, ..Options::default() };
    tla_checker::check(spec, &config, &options, |evaluator| evaluator.clone())
}

fn check_one(spec_path: PathBuf, config_path: PathBuf, library: HashMap<String, PathBuf>) {
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || check(&spec_path, &config_path, &library))
        .unwrap()
        .join()
        .unwrap_or_else(|panic| {
            let message = panic
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| panic.downcast_ref::<&str>().map(|text| text.to_string()))
                .unwrap_or_default();
            Outcome::error(format!("panic: {message}"))
        });
    println!("{}", Reported::from_outcome(&outcome).encode());
}

enum Run {
    Done(Reported),
    Timeout,
    Crash(String),
}

impl Run {
    /// The line the outcomes file has for the run.
    fn encode(&self) -> String {
        match self {
            Run::Done(reported) => reported.encode(),
            Run::Timeout => "timeout".into(),
            Run::Crash(_) => "crash".into(),
        }
    }
}

fn check_in_child(spec: &Path, config: &Path, library_args: &[String], timeout: Duration) -> Run {
    let mut child = Command::new(std::env::current_exe().unwrap())
        .arg("--one")
        .arg(spec)
        .arg(config)
        .args(library_args)
        .current_dir(config.parent().unwrap())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("the runner can run itself");
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if started.elapsed() > timeout {
            let _ = child.kill();
            let _ = child.wait();
            return Run::Timeout;
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    let mut output = String::new();
    let _ = child.stdout.take().unwrap().read_to_string(&mut output);
    match output.lines().last().and_then(Reported::decode) {
        Some(reported) => Run::Done(reported),
        None => Run::Crash(format!("the checker crashed: {status}")),
    }
}

/// tla-ts's record of TLC's result for a model.
struct Expected {
    status: String,
    violation: Option<String>,
    generated: Option<u64>,
    distinct: Option<u64>,
    depth: Option<u64>,
    trace_length: Option<u64>,
    /// How long TLC ran.
    milliseconds: Option<u64>,
}

/// How long TLC may run before an error it reports is the end of its resources, as tla-ts's
/// conformance runner takes it (`--max-tlc-ms`).
const TLC_TIME_LIMIT_MS: u64 = 20_000;

impl Expected {
    fn from_json(record: &serde_json::Value) -> Self {
        let number = |field: &str| record[field].as_u64();
        Self {
            status: record["status"].as_str().unwrap_or_default().to_owned(),
            violation: record["violation"].as_str().map(str::to_owned),
            generated: number("generatedStates"),
            distinct: number("distinctStates"),
            depth: number("depth"),
            trace_length: number("traceLength"),
            milliseconds: number("tlcMilliseconds"),
        }
    }

    /// Whether TLC reached a verdict. TLC errs after a long run only when it runs out of memory
    /// or disk on a state space too large for it, which tla-ts's runner leaves out.
    fn has_verdict(&self) -> bool {
        self.status != "error" || self.milliseconds.unwrap_or(0) <= TLC_TIME_LIMIT_MS
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Verdict {
    Match,
    Mismatch,
    Unsupported,
    /// TLC has no verdict to compare with.
    Unjudged,
    Timeout,
    Crash,
}

impl Verdict {
    fn name(self) -> &'static str {
        match self {
            Verdict::Match => "match",
            Verdict::Mismatch => "mismatch",
            Verdict::Unsupported => "unsupported",
            Verdict::Unjudged => "no-verdict",
            Verdict::Timeout => "timeout",
            Verdict::Crash => "crash",
        }
    }
}

/// tla-ts's `compareOutcome`, with liveness left out: what differs, if anything.
fn compare(expected: &Expected, actual: &Reported) -> (Verdict, Option<String>) {
    if actual.status == Status::Unsupported.name() {
        return (Verdict::Unsupported, actual.message.clone());
    }
    // TLC's liveness checker reports a violated temporal property as either, and fails on a
    // temporal property it can't evaluate. TLC checks the temporal properties before the
    // postconditions.
    let is_liveness_left_out = ["liveness-violation", "property-violation", "error"]
        .contains(&expected.status.as_str())
        && [Status::Success.name(), Status::PostconditionViolation.name()]
            .contains(&actual.status.as_str())
        && actual.has_liveness;
    if is_liveness_left_out {
        return (Verdict::Unsupported, Some("liveness checking".into()));
    }
    if expected.status == "error" {
        return match actual.status.as_str() {
            "error" => (Verdict::Match, None),
            status => (Verdict::Mismatch, Some(format!("expected an error, got {status}"))),
        };
    }
    // TLC exits as for a violated assumption when a postcondition fails.
    let status = match actual.status.as_str() {
        "postcondition-violation" => "assumption-violation",
        status => status,
    };
    if status != expected.status {
        let error =
            actual.message.as_deref().map(|message| format!(" ({message})")).unwrap_or_default();
        return (
            Verdict::Mismatch,
            Some(format!("expected {}, got {}{error}", expected.status, actual.status)),
        );
    }
    let mut differences = Vec::new();
    let mut compare = |field: &str, expected: Option<String>, actual: Option<String>| {
        if let Some(expected) = expected
            && Some(&expected) != actual.as_ref()
        {
            differences.push(format!(
                "{field}: expected {expected}, got {}",
                actual.unwrap_or("none".into())
            ));
        }
    };
    let text = |value: Option<u64>| value.map(|value| value.to_string());
    compare("violation", expected.violation.clone(), actual.violation.clone());
    compare("generatedStates", text(expected.generated), text(actual.generated));
    compare("distinctStates", text(expected.distinct), text(actual.distinct));
    compare("depth", text(expected.depth), text(actual.depth));
    compare("traceLength", text(expected.trace_length), text(actual.trace_length));
    match differences.is_empty() {
        true => (Verdict::Match, None),
        false => (Verdict::Mismatch, Some(differences.join("; "))),
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let first = args.next().expect(USAGE);
    let one = match first.as_str() {
        "--one" => Some((
            PathBuf::from(args.next().expect(USAGE)),
            PathBuf::from(args.next().expect(USAGE)),
        )),
        _ => None,
    };
    let root = PathBuf::from(&first);
    let mut library = HashMap::new();
    let mut library_args = Vec::new();
    let mut expected_path = None;
    let mut outcomes_path = None;
    let mut filter = None;
    let mut timeout = Duration::from_secs(60);
    let mut jobs = std::thread::available_parallelism().map_or(4, |count| count.get());
    while let Some(flag) = args.next() {
        let value = args.next().expect(USAGE);
        match flag.as_str() {
            "--expected" => expected_path = Some(PathBuf::from(value)),
            "--outcomes" => outcomes_path = Some(PathBuf::from(value)),
            "--filter" => filter = Some(value),
            "--timeout" => timeout = Duration::from_secs_f64(value.parse().expect(USAGE)),
            "--jobs" => jobs = value.parse().expect(USAGE),
            "--library" => {
                // Absolute, since each child runs in its model's directory.
                let value = std::fs::canonicalize(&value)
                    .map_or(value, |path| path.to_string_lossy().into_owned());
                let mut files = Vec::new();
                collect(Path::new(&value), &mut files);
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
    if let Some((spec, config)) = one {
        return check_one(spec, config, library);
    }

    let expected_path = expected_path.expect(USAGE);
    let records: Vec<serde_json::Value> =
        serde_json::from_str(&std::fs::read_to_string(expected_path).unwrap()).unwrap();
    let root = std::fs::canonicalize(&root).unwrap_or(root);
    let models: Vec<(String, Expected)> = records
        .iter()
        .filter_map(|record| Some((record["id"].as_str()?.to_owned(), Expected::from_json(record))))
        .filter(|(id, _)| filter.as_ref().is_none_or(|filter| id.contains(filter.as_str())))
        .collect();

    let started = Instant::now();
    let queue = Mutex::new(models.iter());
    let results = Mutex::new(BTreeMap::new());
    std::thread::scope(|scope| {
        for _ in 0..jobs {
            scope.spawn(|| {
                loop {
                    let Some((id, expected)) = queue.lock().unwrap().next() else { break };
                    let config = root.join(id);
                    let spec = config.with_extension("tla");
                    let run = check_in_child(&spec, &config, &library_args, timeout);
                    let (verdict, detail, line) = match &run {
                        _ if !expected.has_verdict() => {
                            let seconds = expected.milliseconds.unwrap_or(0) / 1000;
                            let detail = format!("TLC stopped with an error after {seconds} s");
                            (Verdict::Unjudged, Some(detail), run.encode())
                        }
                        Run::Done(reported) => {
                            let (verdict, detail) = compare(expected, reported);
                            (verdict, detail, run.encode())
                        }
                        Run::Timeout => (Verdict::Timeout, None, run.encode()),
                        Run::Crash(message) => {
                            (Verdict::Crash, Some(message.clone()), run.encode())
                        }
                    };
                    results.lock().unwrap().insert(id.clone(), (verdict, detail, line));
                }
            });
        }
    });
    let results = results.into_inner().unwrap();
    for (id, (verdict, detail, _)) in &results {
        if *verdict != Verdict::Match {
            let detail = detail.as_deref().unwrap_or_default().replace('\n', " ");
            println!("{:<11} {id}  {}", verdict.name(), truncate(&detail, 300));
        }
    }
    let mut tallies: BTreeMap<Verdict, usize> = BTreeMap::new();
    for (verdict, _, _) in results.values() {
        *tallies.entry(*verdict).or_default() += 1;
    }
    let summary: Vec<String> =
        tallies.iter().map(|(verdict, count)| format!("{}: {count}", verdict.name())).collect();
    println!("\n{} models in {:.2?}: {}", results.len(), started.elapsed(), summary.join(", "));
    if let Some(path) = outcomes_path {
        let lines: String = results
            .iter()
            .map(|(id, (verdict, _, line))| format!("{id}\t{}\t{line}\n", verdict.name()))
            .collect();
        std::fs::write(path, lines).unwrap();
    }
}

fn truncate(text: &str, length: usize) -> String {
    match text.char_indices().nth(length) {
        Some((index, _)) => format!("{}...", &text[..index]),
        None => text.to_owned(),
    }
}

fn collect(path: &Path, files: &mut Vec<PathBuf>) {
    if path.is_dir() {
        for entry in std::fs::read_dir(path).into_iter().flatten().flatten() {
            collect(&entry.path(), files);
        }
    } else if path.extension().is_some_and(|found| found == "tla") {
        files.push(path.to_path_buf());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reported(status: Status) -> Reported {
        Reported {
            status: status.name().to_owned(),
            violation: None,
            trace_length: None,
            generated: None,
            distinct: None,
            depth: None,
            message: None,
            has_liveness: false,
        }
    }

    fn expected(record: serde_json::Value) -> Expected {
        Expected::from_json(&record)
    }

    #[test]
    fn encodes_outcomes_in_one_line() {
        let outcome = Reported {
            violation: Some("Inv".into()),
            trace_length: Some(3),
            message: Some("a\tb\nc \\n".into()),
            has_liveness: true,
            ..reported(Status::InvariantViolation)
        };
        let line = outcome.encode();
        assert!(!line.contains('\n'));
        let decoded = Reported::decode(&line).unwrap();
        assert_eq!(decoded.encode(), line);
        assert_eq!(decoded.message.as_deref(), Some("a\tb\nc \\n"));
        assert!(decoded.has_liveness && decoded.generated.is_none());
    }

    #[test]
    fn compares_outcomes_as_tla_ts_does() {
        let success = Reported {
            generated: Some(4),
            distinct: Some(3),
            depth: Some(2),
            ..reported(Status::Success)
        };
        let record = serde_json::json!({
            "status": "success", "generatedStates": 4, "distinctStates": 3, "depth": 2
        });
        assert_eq!(compare(&expected(record), &success).0, Verdict::Match);
        let record = serde_json::json!({
            "status": "success", "generatedStates": 5, "distinctStates": 3, "depth": 2
        });
        assert_eq!(compare(&expected(record), &success).0, Verdict::Mismatch);
        // TLC exits as for a violated assumption when a postcondition fails.
        let postcondition =
            Reported { trace_length: Some(0), ..reported(Status::PostconditionViolation) };
        let record = serde_json::json!({ "status": "assumption-violation", "traceLength": 0 });
        assert_eq!(compare(&expected(record), &postcondition).0, Verdict::Match);
        // What liveness checking would find is left out.
        let record = serde_json::json!({ "status": "liveness-violation", "traceLength": 2 });
        assert_eq!(compare(&expected(record.clone()), &success).0, Verdict::Mismatch);
        let live = Reported { has_liveness: true, ..success };
        assert_eq!(compare(&expected(record), &live).0, Verdict::Unsupported);
        let record = serde_json::json!({ "status": "error" });
        assert_eq!(compare(&expected(record.clone()), &live).0, Verdict::Unsupported);
        assert_eq!(compare(&expected(record), &reported(Status::Error)).0, Verdict::Match);
    }

    #[test]
    fn leaves_out_tlc_running_out_of_resources() {
        let record = serde_json::json!({ "status": "error", "tlcMilliseconds": 300_022 });
        assert!(!expected(record).has_verdict());
        let record = serde_json::json!({ "status": "error", "tlcMilliseconds": 400 });
        assert!(expected(record).has_verdict());
        let record = serde_json::json!({ "status": "success", "tlcMilliseconds": 300_022 });
        assert!(expected(record).has_verdict());
    }
}
