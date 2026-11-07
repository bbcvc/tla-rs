//! Runs tla-rs on each spec in `tests/golden` and compares its output and exit status with what
//! tla-ts's TLC command line printed (`tests/golden/regenerate.sh`), once the lines that name
//! the program, the machine, or SANY's files are left out and times and dates are replaced.

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

fn normalize(output: &str) -> String {
    output
        .lines()
        .filter(|line| !LEFT_OUT.iter().any(|start| line.starts_with(start)))
        .map(|line| replace_duration(&replace_dates(line)))
        .collect::<Vec<_>>()
        .join("\n")
}

fn check(name: &str) {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/golden");
    let expected = std::fs::read_to_string(directory.join(format!("{name}.out"))).unwrap();
    let (status, expected) = expected.split_once('\n').unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_tla-rs"))
        .args([&format!("{name}.tla"), "-seed", "4"])
        .current_dir(&directory)
        .output()
        .unwrap();
    let actual = normalize(&String::from_utf8_lossy(&output.stdout));
    assert_eq!(actual, expected.trim_end_matches('\n'), "the output of {name}");
    let code = output.status.code().unwrap();
    assert_eq!(format!("exit {code}"), status, "the exit status of {name}");
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

macro_rules! golden {
    ($($test:ident: $name:literal,)*) => {
        $(
            #[test]
            fn $test() {
                check($name);
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
}
