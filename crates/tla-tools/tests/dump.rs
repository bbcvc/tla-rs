//! Runs tla-rs with TLC's `-dump` and compares what it writes with what TLC 1.8.0 wrote for the
//! same run, recorded with `-fp 0` so that the fingerprints that name the states match.
//!
//! `tests/dump/graph` holds tla-ts's recordings (`tests/fixtures/state-graph`). Each folder of
//! `tests/statechart` is a run of the statechart skill of cursor/plugins, as tla-ts
//! recorded it (`tests/fixtures/statechart`): the spec, the `ChartRun` module and configuration
//! the skill wrote for it, the graph TLC dumped, and TLC's exit status.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/dump")
}

/// A new, empty directory for what a test writes. Tests run in parallel and several dump one
/// spec, so each call gets a directory of its own.
fn output(name: &str) -> PathBuf {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    let call = CALLS.fetch_add(1, Ordering::Relaxed);
    let directory =
        std::env::temp_dir().join(format!("tla-rs-dump-{}-{call}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).unwrap();
    directory
}

/// Runs tla-rs in `directory` and returns its exit status.
fn run(directory: &Path, args: &[&str]) -> i32 {
    let output = Command::new(env!("CARGO_BIN_EXE_tla-rs"))
        .args(args)
        .current_dir(directory)
        .output()
        .expect("tla-rs runs");
    output.status.code().expect("tla-rs exits")
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

/// Dumps the spec `name` in `tests/dump/graph` with `format` and compares the file with TLC's
/// `expected`.
fn dumps_like_tlc(name: &str, format: Option<&str>, expected: &str, extra: &[&str]) {
    let directory = fixtures().join("graph");
    let out = output(name).join("graph");
    let out = out.to_str().unwrap();
    let spec = format!("{name}.tla");
    let mut args: Vec<&str> = vec![&spec, "-dump"];
    args.extend(format);
    args.push(out);
    args.extend(extra);
    run(&directory, &args);
    let extension = if format.is_some() { "dot" } else { "dump" };
    let written = read(Path::new(&format!("{out}.{extension}")));
    assert_eq!(written, read(&directory.join(expected)), "{name}");
}

#[test]
fn writes_a_deadlocked_counter() {
    dumps_like_tlc("Counter", Some("dot,actionlabels"), "Counter.dot", &[]);
}

#[test]
fn lists_the_states_without_dot() {
    dumps_like_tlc("Counter", None, "Counter.dump", &[]);
}

#[test]
fn colors_every_edge_up_to_an_invariant_violation() {
    dumps_like_tlc("WaterJugs", Some("dot,colorize,actionlabels"), "WaterJugs.dot", &[]);
}

#[test]
fn labels_an_edge_with_the_values_of_the_action_s_parameters() {
    dumps_like_tlc("Mutex", Some("dot,colorize,actionlabels"), "Mutex.dot", &[]);
}

#[test]
fn writes_the_graph_of_one_worker_when_several_are_asked_for() {
    dumps_like_tlc("Mutex", Some("dot,colorize,actionlabels"), "Mutex.dot", &["-workers", "4"]);
}

#[test]
fn labels_a_state_by_its_alias_and_escapes_quotes_and_backslashes() {
    dumps_like_tlc("Labels", Some("dot,colorize,actionlabels"), "Labels.dot", &[]);
}

#[test]
fn names_edges_without_changing_the_states_random_element_chooses() {
    let format = Some("dot,colorize,actionlabels");
    dumps_like_tlc("RandomElementXandY", format, "RandomElementXandY.dot", &["-seed", "4"]);
}

#[test]
fn writes_the_steps_again_when_tlc_replays_a_failed_invariant() {
    dumps_like_tlc("FailedInvariant", Some("dot,actionlabels"), "FailedInvariant.dot", &[]);
}

#[test]
fn leaves_a_snapshot_that_matches_the_finished_graph() {
    let directory = fixtures().join("graph");
    let out = output("snapshot").join("WaterJugs");
    let format = "dot,colorize,actionlabels,snapshot";
    run(&directory, &["WaterJugs.tla", "-dump", format, out.to_str().unwrap()]);
    let snapshot = out.with_file_name("WaterJugs_snapshot.dot");
    assert_eq!(read(&snapshot), read(&directory.join("WaterJugs.dot")));
}

#[test]
fn keeps_the_extension_the_file_has() {
    let directory = fixtures().join("graph");
    let out = output("extension").join("Counter.dot");
    run(&directory, &["Counter.tla", "-dump", "dot,actionlabels", out.to_str().unwrap()]);
    assert_eq!(read(&out), read(&directory.join("Counter.dot")));
}

/// Runs the statechart skill's `-dump` of each recorded spec as the skill runs TLC.
#[test]
fn dumps_the_graphs_the_statechart_skill_reads() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/statechart");
    let mut names: Vec<_> = std::fs::read_dir(&root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.is_dir())
        .collect();
    names.sort();
    assert!(names.len() >= 30, "the statechart fixtures are there");
    let mut failures = Vec::new();
    for directory in names {
        let name = directory.file_name().unwrap().to_string_lossy().into_owned();
        let out = output(&format!("statechart-{name}")).join("graph");
        let args = [
            "-tool",
            "-workers",
            "1",
            "-fp",
            "0",
            "-lncheck",
            "final",
            "-deadlock",
            "-config",
            "ChartRun.cfg",
            "-dump",
            "dot,actionlabels",
            out.to_str().unwrap(),
            "ChartRun",
        ];
        let status = run(&directory, &args);
        let expected_status: i32 = read(&directory.join("ChartRun.exit")).trim().parse().unwrap();
        if read(&out.with_extension("dot")) != read(&directory.join("graph.dot")) {
            failures.push(format!("{name}: the graph differs"));
        }
        if status != expected_status {
            failures.push(format!("{name}: exit {status}, TLC exits {expected_status}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
