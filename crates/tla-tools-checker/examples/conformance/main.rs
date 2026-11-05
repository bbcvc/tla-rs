//! Checks every model TLC was recorded on and compares the outcome with TLC's, as tla-ts's
//! `scripts/conformance.ts` does:
//!
//! ```text
//! cargo run --release -p tla-tools-checker --example conformance -- DIR --expected expected.json
//!     [--library DIR]... [--timeout SECONDS] [--jobs N] [--filter TEXT] [--outcomes FILE]
//! ```
//!
//! `DIR` holds the corpora, and each record of `expected.json` names a model by the path of its
//! configuration relative to it. Each model is checked in a child process in its configuration's
//! directory, as TLC ran there, with TLC's `-seed 4`, so a model that runs too long or crashes
//! only fails itself.
//!
//! `--outcomes FILE` writes a line per model: its id, the verdict, how many milliseconds the
//! child process ran, and what it reported. The run ends with how long the models that match
//! took against how long TLC took on them.
//!
//! The comparison follows `compareOutcome`: an error matches an error, and otherwise the status
//! must agree, then the violated invariant or property, the states generated, the distinct
//! states, the depth, and the length of the trace, where TLC's record has them. A model TLC
//! stopped on with an error after its time limit has no verdict to compare with.

use std::collections::BTreeMap;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use tla_tools_checker::load::{self, Library};
use tla_tools_checker::{Options, Outcome};

use compare::{Expected, Reported, Verdict, compare};

mod compare;
mod timing;

const USAGE: &str = "usage: conformance DIR --expected FILE [--library DIR]... [--timeout SECONDS] \
                     [--jobs N] [--workers N] [--filter TEXT] [--outcomes FILE]";

/// TLC's `-seed` in tla-ts's recordings.
const TLC_SEED: i64 = 4;

fn check(spec_path: &Path, config_path: &Path, library: &Library, workers: usize) -> Outcome {
    let loaded = match load::load(spec_path, config_path, library) {
        Ok(loaded) => loaded,
        Err(error) => return Outcome::error(error.message()),
    };
    // TLC records the expected results with -nowarning.
    let options = Options {
        seed: TLC_SEED,
        classes: loaded.classes,
        variable_order: loaded.variable_order,
        nowarning: true,
        workers,
        ..Options::default()
    };
    tla_tools_checker::check(loaded.spec, &loaded.config, &options, |evaluator| evaluator.clone())
}

/// Checks one model in this process, on a thread with a large stack.
fn check_one(spec_path: PathBuf, config_path: PathBuf, library: Library, workers: usize) {
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || check(&spec_path, &config_path, &library, workers))
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

/// Checks a model in a child process, and how long that took.
fn check_in_child(
    spec: &Path,
    config: &Path,
    library_args: &[String],
    timeout: Duration,
) -> (Run, Duration) {
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
            return (Run::Timeout, started.elapsed());
        }
        std::thread::sleep(Duration::from_millis(1));
    };
    let elapsed = started.elapsed();
    let mut output = String::new();
    let _ = child.stdout.take().unwrap().read_to_string(&mut output);
    let run = match output.lines().last().and_then(Reported::decode) {
        Some(reported) => Run::Done(reported),
        None => Run::Crash(format!("the checker crashed: {status}")),
    };
    (run, elapsed)
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
    let mut library_directories = Vec::new();
    let mut library_args = Vec::new();
    let mut expected_path = None;
    let mut outcomes_path = None;
    let mut filter = None;
    let mut timeout = Duration::from_secs(60);
    let mut jobs = std::thread::available_parallelism().map_or(4, |count| count.get());
    let mut workers = 1;
    while let Some(flag) = args.next() {
        let value = args.next().expect(USAGE);
        match flag.as_str() {
            "--expected" => expected_path = Some(PathBuf::from(value)),
            "--outcomes" => outcomes_path = Some(PathBuf::from(value)),
            "--filter" => filter = Some(value),
            "--timeout" => timeout = Duration::from_secs_f64(value.parse().expect(USAGE)),
            "--jobs" => jobs = value.parse().expect(USAGE),
            "--workers" => {
                workers = value.parse().expect(USAGE);
                library_args.extend(["--workers".to_string(), value]);
            }
            "--library" => {
                // Absolute, since each child runs in its model's directory.
                let value = std::fs::canonicalize(&value)
                    .map_or(value, |path| path.to_string_lossy().into_owned());
                library_directories.push(PathBuf::from(&value));
                library_args.extend(["--library".to_string(), value]);
            }
            _ => panic!("{USAGE}"),
        }
    }
    if let Some((spec, config)) = one {
        return check_one(spec, config, Library::new(&library_directories), workers);
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
                    let (run, elapsed) = check_in_child(&spec, &config, &library_args, timeout);
                    let (verdict, detail, line) = match &run {
                        _ if !expected.has_verdict() => {
                            let seconds = expected.milliseconds.unwrap_or(0) / 1000;
                            let detail = format!("TLC stopped with an error after {seconds} s");
                            (Verdict::Unjudged, Some(detail), run.encode())
                        }
                        Run::Done(reported) => {
                            let (verdict, detail) = compare(expected, reported, workers > 1);
                            (verdict, detail, run.encode())
                        }
                        Run::Timeout => (Verdict::Timeout, None, run.encode()),
                        Run::Crash(message) => {
                            (Verdict::Crash, Some(message.clone()), run.encode())
                        }
                    };
                    let checked = Checked { verdict, detail, line, elapsed };
                    results.lock().unwrap().insert(id.clone(), checked);
                }
            });
        }
    });
    let results: BTreeMap<String, Checked> = results.into_inner().unwrap();
    for (id, checked) in &results {
        if checked.verdict != Verdict::Match {
            let detail = checked.detail.as_deref().unwrap_or_default().replace('\n', " ");
            println!("{:<11} {id}  {}", checked.verdict.name(), truncate(&detail, 300));
        }
    }
    let timings: Vec<timing::Timing> = models
        .iter()
        .filter_map(|(id, expected)| {
            let checked = results.get(id)?;
            (checked.verdict == Verdict::Match).then_some(timing::Timing {
                id,
                ours: checked.elapsed.as_millis() as u64,
                tlc: expected.milliseconds?,
            })
        })
        .collect();
    println!("\n{}", timing::summary(&timings, 10));
    let mut tallies: BTreeMap<Verdict, usize> = BTreeMap::new();
    for checked in results.values() {
        *tallies.entry(checked.verdict).or_default() += 1;
    }
    let summary: Vec<String> =
        tallies.iter().map(|(verdict, count)| format!("{}: {count}", verdict.name())).collect();
    println!("\n{} models in {:.2?}: {}", results.len(), started.elapsed(), summary.join(", "));
    if let Some(path) = outcomes_path {
        let lines: String = results
            .iter()
            .map(|(id, checked)| {
                let milliseconds = checked.elapsed.as_millis();
                format!("{id}\t{}\t{milliseconds}\t{}\n", checked.verdict.name(), checked.line)
            })
            .collect();
        std::fs::write(path, lines).unwrap();
    }
}

/// What checking one model found, with the line the outcomes file has for it.
struct Checked {
    verdict: Verdict,
    detail: Option<String>,
    line: String,
    elapsed: Duration,
}

fn truncate(text: &str, length: usize) -> String {
    match text.char_indices().nth(length) {
        Some((index, _)) => format!("{}...", &text[..index]),
        None => text.to_owned(),
    }
}
