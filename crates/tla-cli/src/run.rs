//! Checks a spec as `java tlc2.TLC` does, printing TLC's messages as it goes, and returns TLC's
//! exit status.

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use tla_checker::load::{self, Library, LoadError, Loaded};
use tla_checker::{Event, Options, Progress};

use crate::args::Args;
use crate::exit;
use crate::printer::{self, Level, Printer};
use crate::result::{self, Liveness};

/// Prints TLC's version and the options of the search.
fn print_banner(printer: &mut Printer, seed: i64) {
    let version = env!("CARGO_PKG_VERSION");
    printer.print(Level::None, &format!("TLC2 Version {version} (rev: tla-rs)"));
    let cores = std::thread::available_parallelism().map_or(1, |count| count.get());
    let (os, arch, pid) = (std::env::consts::OS, std::env::consts::ARCH, std::process::id());
    // tla-rs checks with one worker until the parallel search lands.
    let text = format!(
        "Running breadth-first search Model-Checking with fp 0 and seed {seed} with 1 worker on {cores} cores with 0MB heap and 0MB offheap memory [pid: {pid}] ({os} {arch}, tla-rs, MemFPSet, MemStateQueue)."
    );
    printer.print(Level::None, &text);
}

/// What SANY prints as it reads the modules: each file it parses, and each module it processes,
/// the modules a module uses first.
fn print_parsing(loaded: &Loaded) {
    for (_, path) in &loaded.files {
        let path = std::fs::canonicalize(path).unwrap_or_else(|_| path.clone());
        println!("Parsing file {}", path.display());
    }
    for module in loaded.spec.modules.iter().rev() {
        println!("Semantic processing of module {}", module.name);
    }
}

/// Prints how long TLC ran, which it prints however it ends.
fn print_finished(printer: &mut Printer, started: Instant) {
    let text =
        format!("Finished in {} at ({})", printer::duration(started.elapsed()), printer::now());
    printer.print(Level::None, &text);
}

/// Prints an event of the check, and notes when liveness checking starts.
fn print_event(printer: &mut Printer, liveness: &mut Liveness, event: &Event) {
    let progress = |counts: &tla_checker::Counts| {
        format!(
            "Progress({}) at {}: {} states generated, {} distinct states found, {} states left on queue.",
            counts.depth.max(1),
            printer::now(),
            counts.generated,
            counts.distinct,
            counts.queue
        )
    };
    match event {
        Event::TemporalBranches(branches) => {
            let text = format!(
                "Implied-temporal checking--satisfiability problem has {branches} branches."
            );
            printer.print(Level::None, &text);
        }
        Event::InitialStatesStarted => printer.print(Level::None, "Computing initial states..."),
        Event::InitialStatesComputed { generated, distinct } => {
            let date = printer::now();
            let text = match generated == distinct {
                true => {
                    let plural = if *distinct == 1 { "" } else { "s" };
                    format!(
                        "Finished computing initial states: {distinct} distinct state{plural} generated at {date}."
                    )
                }
                false => {
                    let plural = if *generated == 1 { "" } else { "s" };
                    format!(
                        "Finished computing initial states: {generated} state{plural} generated, with {distinct} of them distinct at {date}."
                    )
                }
            };
            printer.print(Level::None, &text);
        }
        Event::Progress(counts) => printer.print(Level::None, &progress(counts)),
        Event::LivenessStarted { counts, branches, states } => {
            printer.print(Level::None, &progress(counts));
            liveness.started = Some(Instant::now());
            let of = if *branches > 1 { format!("{branches} branches of ") } else { String::new() };
            let total = *branches as u64 * states;
            let text = format!(
                "Checking {of}temporal properties for the complete state space with {total} total distinct states at ({})",
                printer::now()
            );
            printer.print(Level::None, &text);
        }
    }
}

/// Checks the spec `args` names and returns TLC's exit status.
pub fn run(args: &Args) -> i32 {
    let printer = Arc::new(Mutex::new(Printer::new(!args.nowarning)));
    if let Some(fp) = args.fp.filter(|&fp| fp != 0) {
        eprintln!("Error: tla-rs fingerprints states as TLC does with -fp 0, not -fp {fp}.");
        return exit::USAGE_ERROR;
    }
    let started = Instant::now();
    print_banner(&mut printer.lock().unwrap(), args.seed);
    let spec_path = find_spec(&args.spec_path(), &args.library);
    let config_path = args.config_path();
    if !config_path.is_file() {
        let text = format!(
            "TLC encountered the following error when trying to read the configuration file {}:\nFile not found.",
            config_path.display()
        );
        printer.lock().unwrap().print(Level::Error, &text);
        return exit::CONFIG_PARSE_ERROR;
    }
    let library = Library::new(&args.library);
    let loaded = load::load(&spec_path, &config_path, &library);
    let mut loaded = match loaded {
        Ok(loaded) => loaded,
        Err(error) => {
            let mut printer = printer.lock().unwrap();
            let code = match error {
                LoadError::Config(message) => {
                    printer.print(Level::Error, &message);
                    exit::CONFIG_PARSE_ERROR
                }
                LoadError::Parse(message) => {
                    println!("{message}\n");
                    let text = format!("Starting... ({})", printer::now());
                    printer.print(Level::None, &text);
                    printer.print(Level::Error, "Parsing or semantic analysis failed.");
                    exit::SPEC_PARSE_ERROR
                }
            };
            print_finished(&mut printer, started);
            return code;
        }
    };
    print_parsing(&loaded);
    printer.lock().unwrap().print(Level::None, &format!("Starting... ({})", printer::now()));
    if args.deadlock {
        loaded.config.check_deadlock = false;
    }
    let liveness = Arc::new(Mutex::new(Liveness::default()));
    let progress = {
        let (printer, liveness) = (printer.clone(), liveness.clone());
        Progress::new(move |event| {
            print_event(&mut printer.lock().unwrap(), &mut liveness.lock().unwrap(), event);
        })
    };
    let options = Options {
        seed: args.seed,
        classes: std::mem::take(&mut loaded.classes),
        variable_order: loaded.variable_order.take(),
        nowarning: args.nowarning,
        progress,
        ..Options::default()
    };
    let has_variables = !loaded.spec.variables.is_empty();
    let outcome =
        tla_checker::check(loaded.spec, &loaded.config, &options, |evaluator| evaluator.clone());
    let mut printer = printer.lock().unwrap();
    // TLC computes the initial states of a spec without variables, of which there are none.
    if !has_variables && outcome.status == tla_checker::Status::Success {
        let mut liveness = Liveness::default();
        print_event(&mut printer, &mut liveness, &Event::InitialStatesStarted);
        let computed = Event::InitialStatesComputed { generated: 0, distinct: 0 };
        print_event(&mut printer, &mut liveness, &computed);
    }
    result::print_outcome(&mut printer, &outcome, &mut liveness.lock().unwrap());
    print_finished(&mut printer, started);
    exit::for_outcome(&outcome)
}

/// The spec's file: TLC also looks for a spec given by a relative path in the library
/// directories.
fn find_spec(path: &Path, library: &[PathBuf]) -> PathBuf {
    if path.exists() || path.is_absolute() {
        return path.to_path_buf();
    }
    library
        .iter()
        .map(|directory| directory.join(path))
        .find(|candidate| candidate.exists())
        .unwrap_or_else(|| path.to_path_buf())
}
