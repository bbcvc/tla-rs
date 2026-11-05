//! `LET` definitions, whose values the evaluator keeps for the frame the `LET` is evaluated in
//! until a slot they read changes.

mod common;

use common::show;

/// The value of `expr` with `Naturals`, printed as TLC prints it.
fn value(expr: &str) -> String {
    show(&format!("EXTENDS Naturals\nExpr == {expr}"), &["Expr"]).remove(0)
}

#[test]
fn computes_a_let_definition_again_for_each_binding_it_reads() {
    assert_eq!(value("\\A x \\in 1..3 : LET y == x * 2 IN y = 2 * x"), "TRUE");
    assert_eq!(value("{LET y == x + 1 IN y : x \\in 1..3}"), "{2, 3, 4}");
    // A definition reads what the definitions it uses read.
    assert_eq!(value("\\A x \\in 1..3 : LET y == x  z == y + 1 IN z = x + 1"), "TRUE");
    assert_eq!(value("\\A x \\in 1..3 : LET g(k) == k + x  y == g(1) IN y = x + 1"), "TRUE");
    assert_eq!(
        value("\\A x \\in 1..3 : LET y == x IN \\A z \\in 1..2 : LET w == y + z IN w = x + z"),
        "TRUE"
    );
}

#[test]
fn keeps_a_let_definition_that_reads_none_of_the_bindings_that_change() {
    assert_eq!(value("LET n == 3 IN \\A x \\in 1..n : LET m == n * 2 IN m = 6 /\\ x <= n"), "TRUE");
    assert_eq!(
        value(
            "\\A n \\in 1..4 : LET fact[i \\in 0..n] == IF i = 0 THEN 1 ELSE i * fact[i - 1] IN \\A i \\in 1..n : fact[i] >= i"
        ),
        "TRUE"
    );
    assert_eq!(value("\\A n \\in 1..3 : LET f[i \\in 1..n] == i IN DOMAIN f = 1..n"), "TRUE");
}

/// Outside an action, a definition that builds a set with `\cup` is kept as well.
#[test]
fn keeps_sets_a_let_builds_with_cup_in_an_expression() {
    assert_eq!(
        value("\\A x \\in 1..3 : LET y == {x} \\cup {0} IN y = {0, x} /\\ x \\in y"),
        "TRUE"
    );
}
