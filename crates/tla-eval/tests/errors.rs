//! Evaluation errors, worded as TLC words them and located at the expression that failed. Where
//! TLC's message names the expression, it does so as SANY does: by its range, or for a numeral
//! by its text.

mod common;

use common::{error, eval, evaluator};

fn message(expr: &str) -> String {
    error(expr).message
}

/// SANY's range of the first occurrence of `part` in `expr`, which `common::error` defines on
/// line 2 of module `Test`, after `Expr == `.
fn range(expr: &str, part: &str) -> String {
    let start = 9 + expr.find(part).expect("part of the expression");
    format!("line 2, col {start} to line 2, col {} of module Test", start + part.len() - 1)
}

/// `message` followed by the range of the whole expression.
fn ranged(expr: &str, message: &str) -> String {
    format!("{message}\n{}", range(expr, expr))
}

#[test]
fn rejects_non_boolean_conditions() {
    let condition = "IF 1 THEN 2 ELSE 3";
    assert_eq!(
        message(condition),
        ranged(
            condition,
            "A non-boolean expression (an integer) was used as the condition of an IF."
        )
    );
    let case = "CASE {} -> 1 [] OTHER -> 2";
    assert_eq!(
        message(case),
        format!(
            "A non-boolean expression (a set of the form {{e1, ... ,eN}}) was used as a condition of a CASE. {}",
            range(case, "{}")
        )
    );
    let exhausted = "CASE FALSE -> 1";
    assert_eq!(
        message(exhausted),
        ranged(exhausted, "Attempted to evaluate a CASE with no conditions true.")
    );
    assert_eq!(message("~ 1"), "~ expects a boolean but received 1");
    assert_eq!(
        message("<<>> => TRUE"),
        "Expected the left side of => to be a boolean but found <<>>"
    );
    assert_eq!(message("TRUE <=> 2"), "<=> expects a boolean but received 2");
    assert_eq!(
        message("\\A x \\in {1} : x"),
        "Expected the body of \\A to be a boolean but found 1"
    );
    assert_eq!(
        message("{x \\in {1} : x}"),
        "Expected a set filter predicate to be a boolean but found 1"
    );
}

#[test]
fn words_junction_errors_by_form() {
    let infix = "TRUE /\\ 1";
    assert_eq!(
        message(infix),
        ranged(
            infix,
            "Attempted to evaluate an expression of form P /\\ Q when Q was\nan integer."
        )
    );
    let parenthesized = "(TRUE) /\\ 1";
    assert_eq!(
        message(parenthesized),
        ranged(
            parenthesized,
            "Attempted to evaluate an expression of form P /\\ Q when Q was\nan integer."
        )
    );
    let chain = "{} \\/ TRUE \\/ FALSE";
    assert_eq!(
        message(chain),
        format!(
            "Attempted to evaluate an expression of form P \\/ Q when P was\na set of the form {{e1, ... ,eN}}.\n{}",
            range(chain, "{} \\/ TRUE")
        )
    );
    assert_eq!(
        message("/\\ TRUE\n        /\\ \"s\""),
        "A non-boolean expression (a string) was used as a formula in a conjunction.\nline 3, col 12 to line 3, col 14 of module Test"
    );
    assert_eq!(
        message("\\/ FALSE\n        \\/ 2"),
        "A non-boolean expression (an integer) was used as a formula in a disjunction.\n2"
    );
}

#[test]
fn fails_to_choose_or_enumerate() {
    let unsatisfied = "CHOOSE x \\in {1, 2} : FALSE";
    assert_eq!(
        message(unsatisfied),
        ranged(
            unsatisfied,
            "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P."
        )
    );
    let infinite = "CHOOSE x \\in STRING : TRUE";
    assert_eq!(
        message(infinite),
        ranged(
            infinite,
            "Attempted to compute the value of an expression of\nform CHOOSE x \\in S: P, but S was not enumerable."
        )
    );
    assert_eq!(
        message("CHOOSE x : TRUE"),
        "TLC cannot evaluate an unbounded CHOOSE at line 2, column 9"
    );
    assert_eq!(
        message("\\E x : TRUE"),
        "TLC cannot evaluate an unbounded quantifier at line 2, column 9"
    );
    let strings = "\\A x \\in STRING : TRUE";
    assert_eq!(
        message(strings),
        format!(
            "TLC encountered a non-enumerable quantifier bound\nSTRING.\n{}",
            range(strings, "STRING")
        )
    );
    assert_eq!(
        message("\\E x \\in 1 : TRUE"),
        "TLC encountered a non-enumerable quantifier bound\n1.\n1"
    );
    assert_eq!(
        message("{s \\in SUBSET {1} : s} = {}"),
        "Expected a set filter predicate to be a boolean but found {}"
    );
}

#[test]
fn rejects_misapplied_functions_and_records() {
    assert_eq!(
        message("1[2]"),
        ranged("1[2]", "A non-function (an integer) was applied as a function.")
    );
    assert_eq!(
        message("DOMAIN {}"),
        ranged(
            "DOMAIN {}",
            "Attempted to apply the operator DOMAIN to a non-function\n(a set of the form {e1, ... ,eN})"
        )
    );
    assert_eq!(
        message("[a |-> 1].b"),
        ranged(
            "[a |-> 1].b",
            "Attempted to select nonexistent field \"b\" from the record\n[a |-> 1]"
        )
    );
    assert_eq!(
        message("{1}.a"),
        ranged("{1}.a", "Attempted to select field \"a\" from a non-record value {1}")
    );
    assert_eq!(
        message("<<1>>.a"),
        "Attempted to apply function with integer domain to the non-integer argument \"a\""
    );
    assert_eq!(
        message("{1} \\subseteq 1 /\\ 1 \\subseteq {1}"),
        "Attempted to check if the value:\n1\nis an element of the integer 1"
    );
    assert_eq!(
        message("STRING \\subseteq {1}"),
        ranged(
            "STRING \\subseteq {1}",
            "Attempted to evaluate an expression of form S \\subseteq T, but S was not enumerable."
        )
    );
    assert_eq!(message("UNION 1"), "UNION expects a set but received 1");
    assert_eq!(
        message("1 = \"a\""),
        "Attempted to check equality of integer 1 with non-integer:\n\"a\""
    );
}

#[test]
fn rejects_what_tlc_cannot_evaluate_in_a_state() {
    let temporal = "TLC cannot evaluate a temporal formula in a state at line 2, column 9";
    assert_eq!(message("[]TRUE"), temporal);
    assert_eq!(message("<>TRUE"), temporal);
    assert_eq!(message("\\EE x : TRUE"), temporal);
    assert_eq!(
        message("TRUE ~> TRUE"),
        "TLC cannot evaluate a temporal formula such as ~> in a state"
    );
    assert_eq!(message("ENABLED TRUE"), "ENABLED is not supported yet");
    assert_eq!(
        message("2147483648"),
        "TLC can't handle a number this big: 2147483648 at line 2, column 9"
    );
}

#[test]
fn locates_errors_at_the_innermost_expression() {
    let evaluator = evaluator(
        "Fails(s) == CHOOSE x \\in s : FALSE\nExpr == <<1, Fails({1})>>\nIndex == <<1>>[3]",
    );
    let error = eval(&evaluator, "Expr").unwrap_err();
    assert_eq!((error.module.as_str(), error.line, error.column), ("Test", 2, 13));
    let error = eval(&evaluator, "Index").unwrap_err();
    assert_eq!((error.line, error.column), (4, 10));
    assert_eq!(
        error.to_string(),
        "Attempted to apply tuple\n<<1>>\nto argument 3, which is out of bounds.\nline 4, column 10 of module Test"
    );
}
