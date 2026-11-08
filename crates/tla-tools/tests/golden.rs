//! Runs tla-rs on each spec in `tests/golden` and compares its output and exit status with what
//! tla-ts's TLC command line printed (`tests/golden/regenerate.sh`), and under `-tool` with what
//! TLC itself printed (`tests/golden/regenerate-tool.sh`), once the lines that name the program,
//! the machine, or SANY's files are left out and times, dates, and rates are replaced.

use std::path::Path;
use std::process::Command;

const LEFT_OUT: &[&str] = &[
    "TLC2 Version",
    "Running breadth-first",
    "Parsing file",
    "Semantic processing",
    "Linting of module",
];

/// Replaces each `2024-01-31 12:34:56` with `DATE`.
fn replace_dates(line: &str) -> String {
    let bytes = line.as_bytes();
    let shape = b"dddd-dd-dd dd:dd:dd";
    let matches = |at: usize| {
        bytes.len() >= at + shape.len()
            && shape.iter().zip(&bytes[at..]).all(|(&expected, &byte)| match expected {
                b'd' => byte.is_ascii_digit(),
                _ => byte == expected,
            })
    };
    let (mut result, mut index) = (String::new(), 0);
    while index < bytes.len() {
        if matches(index) {
            result.push_str("DATE");
            index += shape.len();
        } else {
            let char = line[index..].chars().next().unwrap();
            result.push(char);
            index += char.len_utf8();
        }
    }
    result
}

/// Replaces the duration in `... in 00s at ...` with `TIME`.
fn replace_duration(line: &str) -> String {
    let Some(start) = line.find(" in ") else { return line.to_owned() };
    let rest = &line[start + 4..];
    let Some(end) = rest.find(" at ") else { return line.to_owned() };
    let duration = &rest[..end];
    if duration.is_empty() || !duration.chars().all(|char| "0123456789dhmins ".contains(char)) {
        return line.to_owned();
    }
    format!("{} in TIME{}", &line[..start], &rest[end..])
}

/// Replaces each rate in `(3,011 s/min)` or `(2,316 ds/min)`, which TLC prints under `-tool`,
/// with `RATE`.
fn replace_rates(line: &str) -> String {
    let mut result = String::new();
    let mut rest = line;
    while let Some(start) = rest.find('(') {
        result.push_str(&rest[..=start]);
        rest = &rest[start + 1..];
        let digits = rest.find(|char: char| !char.is_ascii_digit() && char != ',').unwrap_or(0);
        let unit =
            [" s/min)", " ds/min)"].into_iter().find(|unit| rest[digits..].starts_with(unit));
        if digits > 0 && unit.is_some() {
            result.push_str("RATE");
            rest = &rest[digits..];
        }
    }
    result.push_str(rest);
    result
}

fn normalize(output: &str) -> String {
    output
        .lines()
        .filter(|line| !LEFT_OUT.iter().any(|start| line.starts_with(start)))
        .map(|line| replace_rates(&replace_duration(&replace_dates(line))))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Checks the spec `name` with the options `options`, against the expected output in the file
/// `name` with `extension`.
fn check(name: &str, extension: &str, options: &[&str]) {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/golden");
    let expected = std::fs::read_to_string(directory.join(format!("{name}{extension}"))).unwrap();
    let (status, expected) = expected.split_once('\n').unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_tla-rs"))
        .args([&format!("{name}.tla"), "-seed", "4"])
        .args(options)
        .current_dir(&directory)
        .output()
        .unwrap();
    let actual = normalize(&String::from_utf8_lossy(&output.stdout));
    assert_eq!(actual, expected.trim_end_matches('\n'), "the output of {name} {options:?}");
    let code = output.status.code().unwrap();
    assert_eq!(format!("exit {code}"), status, "the exit status of {name} {options:?}");
}

#[test]
fn normalizes_times_and_dates() {
    let line = "Finished in 01min 05s at (2024-01-31 12:34:56)";
    assert_eq!(replace_duration(&replace_dates(line)), "Finished in TIME at (DATE)");
    let line = "Finished checking temporal properties in 00s at 2024-01-31 12:34:56";
    assert_eq!(
        replace_duration(&replace_dates(line)),
        "Finished checking temporal properties in TIME at DATE"
    );
}

#[test]
fn normalizes_rates() {
    let line = "Progress(5) at DATE: 13 states generated (3,011 s/min), 10 distinct states found \
                (2,316 ds/min), 2 states left on queue.";
    let normalized = "Progress(5) at DATE: 13 states generated (RATE s/min), 10 distinct states \
                      found (RATE ds/min), 2 states left on queue.";
    assert_eq!(replace_rates(line), normalized);
    assert_eq!(replace_rates("(a) (12)"), "(a) (12)");
}

/// For each spec, a test of its output as TLC prints it and one under `-tool`.
macro_rules! golden {
    ($($test:ident: $name:literal,)*) => {
        $(
            mod $test {
                #[test]
                fn plain() {
                    super::check($name, ".out", &[]);
                }

                #[test]
                fn tool() {
                    super::check($name, ".tool.out", &["-tool"]);
                }
            }
        )*
    };
}

golden! {
    invariant_violation: "Counter",
    action_labels_and_pretty_printed_values: "Labels",
    deadlock: "Deadlock",
    success_with_liveness: "Success",
    assumption_violation: "Assumption",
    liveness_lasso: "Lasso",
    liveness_stuttering: "Stutter",
    action_property_violation: "ActionProperty",
    initial_state_violation: "InitialState",
    spec_without_variables: "Constants",
    print_and_print_t: "Print",
    alias: "Alias",
    alias_of_a_lasso: "AliasLasso",
    call_stack_of_an_error_in_an_action: "CallStack",
    call_stack_of_an_error_in_the_initial_predicate: "InitCallStack",
    semantic_error: "SemanticError",
    missing_module: "MissingModule",
    invariant_that_fails_to_evaluate: "InvariantError",
    initial_state_a_check_fails_on: "InitialStateError",
    action_property_that_fails_to_evaluate: "ActionPropertyError",
}
