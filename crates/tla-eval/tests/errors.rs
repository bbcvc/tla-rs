//! Evaluation errors, worded as TLC words them and located at the expression that failed.

mod common;

use common::{error, eval, evaluator};

fn message(expr: &str) -> String {
    error(expr).message
}

#[test]
fn rejects_non_boolean_conditions() {
    assert_eq!(
        message("IF 1 THEN 2 ELSE 3"),
        "A non-boolean expression (an integer) was used as the condition of an IF."
    );
    assert_eq!(
        message("CASE {} -> 1 [] OTHER -> 2"),
        "A non-boolean expression (a set of the form {e1, ... ,eN}) was used as a condition of a CASE."
    );
    assert_eq!(message("CASE FALSE -> 1"), "Attempted to evaluate a CASE with no conditions true.");
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
    assert_eq!(
        message("TRUE /\\ 1"),
        "Attempted to evaluate an expression of form P /\\ Q when Q was\nan integer."
    );
    assert_eq!(
        message("{} \\/ TRUE"),
        "Attempted to evaluate an expression of form P \\/ Q when P was\na set of the form {e1, ... ,eN}."
    );
    assert_eq!(
        message("/\\ TRUE\n        /\\ \"s\""),
        "A non-boolean expression (a string) was used as a formula in a conjunction."
    );
    assert_eq!(
        message("\\/ FALSE\n        \\/ <<1>>"),
        "A non-boolean expression (a tuple) was used as a formula in a disjunction."
    );
}

#[test]
fn fails_to_choose_or_enumerate() {
    assert_eq!(
        message("CHOOSE x \\in {1, 2} : FALSE"),
        "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P."
    );
    assert_eq!(
        message("CHOOSE x \\in STRING : TRUE"),
        "Attempted to compute the value of an expression of\nform CHOOSE x \\in S: P, but S was not enumerable."
    );
    assert_eq!(message("CHOOSE x : TRUE"), "TLC cannot evaluate an unbounded CHOOSE");
    assert_eq!(message("\\E x : TRUE"), "TLC cannot evaluate an unbounded quantifier");
    assert_eq!(
        message("\\A x \\in STRING : TRUE"),
        "TLC encountered a non-enumerable quantifier bound\nSTRING."
    );
    assert_eq!(
        message("\\E x \\in 1 : TRUE"),
        "TLC encountered a non-enumerable quantifier bound\n1."
    );
    assert_eq!(
        message("{s \\in SUBSET {1} : s} = {}"),
        "Expected a set filter predicate to be a boolean but found {}"
    );
}

#[test]
fn rejects_misapplied_functions_and_records() {
    assert_eq!(message("1[2]"), "A non-function (an integer) was applied as a function.");
    assert_eq!(
        message("DOMAIN {}"),
        "Attempted to apply the operator DOMAIN to a non-function\n(a set of the form {e1, ... ,eN})"
    );
    assert_eq!(
        message("[a |-> 1].b"),
        "Attempted to select nonexistent field \"b\" from the record\n[a |-> 1]"
    );
    assert_eq!(message("{1}.a"), "Attempted to select field \"a\" from a non-record value {1}");
    assert_eq!(
        message("<<1>>.a"),
        "Attempted to apply function with integer domain to the non-integer argument \"a\""
    );
    assert_eq!(
        message("{1} \\subseteq 1 /\\ 1 \\subseteq {1}"),
        "Attempted to check if the value:\n1\nis an element of integer 1"
    );
    assert_eq!(
        message("STRING \\subseteq {1}"),
        "Attempted to evaluate an expression of form S \\subseteq T, but S was not enumerable."
    );
    assert_eq!(message("UNION 1"), "UNION expects a set but received 1");
    assert_eq!(
        message("1 = \"a\""),
        "Attempted to check equality of integer 1 with non-integer:\n\"a\""
    );
}

#[test]
fn rejects_what_tlc_cannot_evaluate_in_a_state() {
    assert_eq!(message("[]TRUE"), "TLC cannot evaluate a temporal formula in a state");
    assert_eq!(message("<>TRUE"), "TLC cannot evaluate a temporal formula in a state");
    assert_eq!(
        message("TRUE ~> TRUE"),
        "TLC cannot evaluate a temporal formula such as ~> in a state"
    );
    assert_eq!(message("ENABLED TRUE"), "ENABLED is not supported yet");
    assert_eq!(message("\\EE x : TRUE"), "TLC cannot evaluate a temporal formula in a state");
    assert_eq!(message("2147483648"), "TLC can't handle a number this big: 2147483648");
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
