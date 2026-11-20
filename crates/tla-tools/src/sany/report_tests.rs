//! SANY's report of the errors and warnings it finds in a spec, ported from tla-ts
//! `tests/unit/sany-report.test.ts`. The expected reports are what SANY prints for the same
//! modules.

use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

use tla_tools_checker::load::{self, Library, Modules};

use super::*;

/// Writes each module to its own file, then reports on the first one as tla-ts's `getSanyReport`
/// does without the lines that name the files and modules: the messages of the semantic
/// analysis after each module. Returns whether SANY rejects the spec.
fn report(modules: &[(&str, &str)]) -> (String, bool) {
    static RUNS: AtomicUsize = AtomicUsize::new(0);
    let run = RUNS.fetch_add(1, Ordering::Relaxed);
    let directory: PathBuf =
        std::env::temp_dir().join(format!("tla-rs-sany-report-{}-{run}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    for (name, source) in modules {
        std::fs::write(directory.join(format!("{name}.tla")), source).unwrap();
    }
    let path = directory.join(format!("{}.tla", modules[0].0));
    let loaded = load::load_spec(&path, &Library::new(&[]));
    std::fs::remove_dir_all(&directory).unwrap();
    match loaded {
        Ok(read) => (text(&read.modules), false),
        Err(failure) => {
            let kind = failure.error.as_ref().map(|error| error.kind);
            assert_eq!(kind, Some(ErrorKind::Semantic), "{}", failure.message);
            (text(&failure.modules), true)
        }
    }
}

fn text(modules: &Modules) -> String {
    let mut out = String::new();
    analysis_report(&modules.order.analyzed, &modules.messages, &mut out);
    out.split_inclusive('\n')
        .filter(|line| !line.starts_with("Semantic processing of module "))
        .collect()
}

fn lines(lines: &[&str]) -> String {
    lines.iter().map(|line| format!("{line}\n")).collect()
}

fn module(name: &str, body: &str) -> String {
    format!("---- MODULE {name} ----\n{body}\n====\n")
}

#[test]
fn reports_nothing_for_a_spec_sany_accepts() {
    let fine = module(
        "Fine",
        "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nSpec == Init /\\ [][Next]_x",
    );
    assert_eq!(report(&[("Fine", &fine)]), (String::new(), false));
}

#[test]
fn reports_an_unresolved_infix_operator_twice() {
    let (text, is_failed) = report(&[("Infix", &module("Infix", "VARIABLE x\nOp == x @@ x"))]);
    assert!(is_failed);
    assert_eq!(
        text,
        lines(&[
            "Semantic errors:",
            "",
            "*** Errors: 2",
            "",
            "line 3, col 9 to line 3, col 10 of module Infix",
            "",
            "Could not find declaration or definition of symbol '@@'.",
            "",
            "",
            "line 3, col 7 to line 3, col 12 of module Infix",
            "",
            "Couldn't resolve infix operator symbol `@@'.",
            "",
            "",
        ])
    );
}

#[test]
fn names_an_unresolved_operator_as_it_is_spelled() {
    for operator in ["\\geq", "=<", "(+)", "\\circ", "!!"] {
        let (text, _) = report(&[("Infix", &module("Infix", &format!("Op == 1 {operator} 2")))]);
        let symbol = format!("Could not find declaration or definition of symbol '{operator}'.");
        let application = format!("Couldn't resolve infix operator symbol `{operator}'.");
        assert!(text.contains(&symbol) && text.contains(&application), "{operator}: {text}");
    }
}

#[test]
fn reports_an_operator_applied_like_a_function_as_unknown() {
    let (text, _) = report(&[("M", &module("M", "x == @@(1, 2)"))]);
    assert!(
        text.contains("*** Errors: 1\n\nline 2, col 6 to line 2, col 7 of module M\n\nUnknown operator: `@@'.\n"),
        "{text}"
    );
}

#[test]
fn reports_a_multiply_defined_operator_with_a_warning_and_an_error() {
    let (text, is_failed) = report(&[("Twice", &module("Twice", "Op == 1\nOp == 2"))]);
    assert!(is_failed);
    assert_eq!(
        text,
        lines(&[
            "*** Warnings: 1",
            "",
            "line 3, col 1 to line 3, col 7 of module Twice",
            "",
            "Multiple declarations or definitions for symbol Op.  ",
            "This duplicates the one at line 2, col 1 to line 2, col 7 of module Twice.",
            "",
            "",
            "",
            "Semantic errors:",
            "",
            "*** Errors: 1",
            "",
            "line 3, col 1 to line 3, col 7 of module Twice",
            "",
            "Operator Op already defined or declared.",
            "",
            "",
        ])
    );
}

#[test]
fn reads_a_definition_of_a_built_in_prefix_operator_and_rejects_it() {
    for (operator, name) in [("<>", "<>"), ("SUBSET", "SUBSET")] {
        let definition = format!("{operator} a == a");
        let (text, is_failed) = report(&[("Prefix", &module("Prefix", &definition))]);
        let location =
            format!("line 2, col 1 to line 2, col {} of module Prefix", definition.len());
        assert!(is_failed);
        assert_eq!(
            text,
            lines(&[
                "Semantic errors:",
                "",
                "*** Errors: 2",
                "",
                &location,
                "",
                &format!("Operator {name} already defined or declared."),
                "",
                "",
                &location,
                "",
                &format!("Symbol {name} is a built-in operator, and cannot be redefined."),
                "",
                "",
            ]),
            "{operator}"
        );
    }
}

#[test]
fn reports_what_is_declared_recursive_but_left_undefined() {
    for (body, name, range, count) in [
        ("RECURSIVE F(_)", "F", "line 3, col 11 to line 3, col 14", 1),
        ("RECURSIVE F(_)\nF(x) == 1\nRECURSIVE F(_)", "F", "line 5, col 11 to line 5, col 14", 1),
        ("RECURSIVE F(_)\nF[x \\in Nat] == 1", "F", "line 3, col 11 to line 3, col 14", 2),
        ("A == LET RECURSIVE G(_) IN 1", "G", "line 3, col 20 to line 3, col 23", 1),
    ] {
        let source = module("M", &format!("EXTENDS Naturals\n{body}"));
        let (text, _) = report(&[("M", &source)]);
        assert!(text.contains(&format!("*** Errors: {count}\n")), "{body}: {text}");
        let error = format!(
            "{range} of module M\n\nSymbol {name} declared in RECURSIVE statement but not defined.\n"
        );
        assert!(text.contains(&error), "{body}: {text}");
    }
}

#[test]
fn takes_an_instance_between_a_recursive_declaration_and_its_definition() {
    let body = "EXTENDS Naturals\nRECURSIVE F(_)\nI == INSTANCE Naturals\nF(n) == IF n = 0 THEN 0 ELSE F(n-1)";
    assert!(!report(&[("M", &module("M", body))]).1);
}

#[test]
fn takes_the_parentheses_of_an_operator_s_only_argument_for_the_operator_s_own() {
    let body = "F(y) == y\nOp(G(_)) == G(1)\nA == Op(F)";
    assert_eq!(report(&[("M", &module("M", body))]), (String::new(), false));
}

#[test]
fn reports_actions_used_as_temporal_formulas() {
    let body = "VARIABLE x\nA == x' ~> []x\nB == [](x')";
    let (text, is_failed) = report(&[("Leads", &module("Leads", body))]);
    assert!(is_failed);
    assert_eq!(
        text,
        lines(&[
            "Semantic errors:",
            "",
            "*** Errors: 2",
            "",
            "line 3, col 6 to line 3, col 14 of module Leads",
            "",
            "Action used where only temporal formula or state predicate allowed.",
            "",
            "",
            "line 4, col 6 to line 4, col 11 of module Leads",
            "",
            "[] followed by action not of form [A]_v.",
            "",
            "",
        ])
    );
}

#[test]
fn checks_the_level_of_an_operator_applied_to_an_always_action() {
    let body = "VARIABLE x\nL == SF_x([](x' = 1))";
    let (text, _) = report(&[("Strong", &module("Strong", body))]);
    assert!(text.contains("*** Errors: 1\n"), "{text}");
    assert!(!text.contains("Level error in applying operator $SF"), "{text}");
}

#[test]
fn reports_a_level_error_in_a_module_and_none_in_the_modules_after_it() {
    let inner = module("Inner", "VARIABLE x\nA == [](x')");
    let outer = module("Outer", "EXTENDS Inner\nB == [](x')");
    let (text, _) = report(&[("Outer", &outer), ("Inner", &inner)]);
    assert!(text.contains("*** Errors: 1\n\nline 3, col 6 to line 3, col 11 of module Inner\n"));
    assert!(!text.contains("of module Outer"), "{text}");
}

#[test]
fn binds_no_bound_identifier_in_the_body_of_a_function_named_by_a_parameter() {
    let body = "F(it, S) == LET it[s \\in S] == s IN it";
    let (text, _) = report(&[("Fold", &module("Fold", body))]);
    assert_eq!(
        text,
        lines(&[
            "Semantic errors:",
            "",
            "*** Errors: 2",
            "",
            "line 2, col 17 to line 2, col 32 of module Fold",
            "",
            "Function name `it' already defined or declared.",
            "",
            "",
            "line 2, col 32 to line 2, col 32 of module Fold",
            "",
            "Unknown operator: `s'.",
            "",
            "",
        ])
    );
}

#[test]
fn binds_the_bound_identifiers_in_the_body_of_a_function_whose_name_is_already_defined() {
    let body = "f[x \\in {1}] == x\nf[x \\in {1}] == x";
    let (text, _) = report(&[("Twice", &module("Twice", body))]);
    assert_eq!(
        text,
        lines(&[
            "Semantic errors:",
            "",
            "*** Errors: 1",
            "",
            "line 3, col 1 to line 3, col 17 of module Twice",
            "",
            "Function name `f' already defined or declared.",
            "",
            "",
        ])
    );
}

#[test]
fn reports_a_substitution_above_the_level_the_instantiated_module_allows() {
    let outer = module("Outer", "VARIABLE x\nI == INSTANCE Inner WITH C <- [](x = 0)");
    let inner = module("Inner", "CONSTANT C\nASSUME C = {}");
    let (text, is_failed) = report(&[("Outer", &outer), ("Inner", &inner)]);
    assert!(is_failed);
    assert_eq!(
        text,
        lines(&[
            "Semantic errors:",
            "",
            "*** Errors: 1",
            "",
            "line 3, col 1 to line 3, col 39 of module Outer",
            "",
            "Level error in instantiating module 'Inner':",
            "The level of the expression or operator substituted for 'C' ",
            "must be at most 2.",
            "",
            "",
        ])
    );
}

#[test]
fn reports_every_unknown_name_of_every_definition() {
    let body = (0..12).map(|index| format!("D{index} == u{index}")).collect::<Vec<_>>();
    let (text, _) = report(&[("Broken", &module("Broken", &body.join("\n")))]);
    assert!(
        text.starts_with("Semantic errors:\n\n*** Errors: 12\n\nline 2, col 7 to line 2, col 8 of module Broken\n\nUnknown operator: `u0'.\n"),
        "{text}"
    );
}

#[test]
fn reports_the_errors_of_a_module_after_those_of_the_modules_analyzed_before_it() {
    let root = module("Root", "A == a\nI == INSTANCE Other\nB == b");
    let other = module("Other", "C == c");
    let (text, _) = report(&[("Root", &root), ("Other", &other)]);
    let after_other = "Semantic errors:\n\n*** Errors: 1\n\nline 2, col 6 to line 2, col 6 of module Other\n\nUnknown operator: `c'.\n\n\n";
    assert!(text.starts_with(after_other), "{text}");
    let errors: Vec<&str> = text[after_other.len()..]
        .lines()
        .filter(|line| line.starts_with("Unknown operator"))
        .collect();
    assert_eq!(
        errors,
        ["Unknown operator: `c'.", "Unknown operator: `a'.", "Unknown operator: `b'."]
    );
}

#[test]
fn locates_the_unknown_operator_of_an_instance_from_the_instance_s_name() {
    let r = module("R", "CONSTANT c");
    for (body, range) in [
        ("Z(c) == INSTANCE R\nx == Z(7)!Nope", "line 3, col 6 to line 3, col 14"),
        ("Z == INSTANCE R WITH c <- 1\nx == Z!Nope", "line 3, col 6 to line 3, col 11"),
    ] {
        let (text, _) = report(&[("M", &module("M", body)), ("R", &r)]);
        let error = format!("{range} of module M\n\nUnknown operator: `Z!Nope'.\n");
        assert!(text.contains(&error), "{body}: {text}");
    }
}
