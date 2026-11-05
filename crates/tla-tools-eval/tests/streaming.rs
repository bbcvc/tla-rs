//! Quantifiers and `CHOOSE` over sets large enough that the evaluator builds their elements one
//! at a time, compared with the same over the sets fully enumerated.

mod common;

use common::show;

/// The value of `expr` with `Naturals`, printed as TLC prints it.
fn value(expr: &str) -> String {
    show(&format!("EXTENDS Naturals\nExpr == {expr}"), &["Expr"]).remove(0)
}

/// `CHOOSE x \in set : predicate` picks what it picks from `{y : y \in set}`, a set enumeration
/// that lists every element of `set` in TLC's order before `CHOOSE` tests any.
fn assert_chooses(set: &str, predicate: &str, expected: &str) {
    let streamed = value(&format!("CHOOSE x \\in {set} : {predicate}"));
    let enumerated = value(&format!("CHOOSE x \\in {{y : y \\in {set}}} : {predicate}"));
    assert_eq!(streamed, enumerated, "CHOOSE x \\in {set} : {predicate}");
    assert_eq!(streamed, expected, "CHOOSE x \\in {set} : {predicate}");
}

#[test]
fn chooses_from_large_sets_of_functions_in_tlc_order() {
    assert_chooses("[1..4 -> 1..17]", "x[2] = 17 /\\ x[4] = 3", "<<1, 17, 1, 3>>");
    assert_chooses(
        "[{\"a\", \"b\", \"c\", \"d\"} -> 1..17]",
        "x[\"b\"] = 5 /\\ x[\"d\"] > 15",
        "[a |-> 1, b |-> 5, c |-> 1, d |-> 16]",
    );
}

#[test]
fn chooses_from_large_sets_of_records_and_tuples_in_tlc_order() {
    assert_chooses("[a : 1..300, b : 1..300]", "x.a + x.b = 400", "[a |-> 100, b |-> 300]");
    assert_chooses("(1..300) \\X (1..300)", "x[1] * x[2] = 1000", "<<4, 250>>");
    assert_chooses(
        "(1..50) \\X {\"b\", \"a\"} \\X (1..900)",
        "x[2] = \"b\" /\\ x[3] = x[1] + 2",
        "<<1, \"b\", 3>>",
    );
}

#[test]
fn chooses_from_large_power_sets_in_tlc_order() {
    assert_chooses("SUBSET (1..17)", "17 \\in x /\\ 3 \\in x /\\ 5 \\in x", "{3, 5, 17}");
    assert_chooses("SUBSET (1..17)", "x # {} /\\ 1 \\notin x", "{2}");
}

/// TLC enumerates a power set by size and then in the order of its base without building it, so
/// a quantifier over the subsets of more than 30 elements stops at its first witness.
#[test]
fn stops_at_the_first_witness_in_power_sets_too_large_to_build() {
    assert_eq!(value("CHOOSE s \\in SUBSET (1..40) : 3 \\in s /\\ 39 \\in s"), "{3, 39}");
    assert_eq!(value("\\E s \\in SUBSET (1..40) : s = {2, 5, 40}"), "TRUE");
    assert_eq!(value("\\A s \\in SUBSET (1..40) : s = {} \\/ 1 \\in s \\/ 2 \\in s"), "FALSE");
}

#[test]
fn quantifies_over_large_sets() {
    assert_eq!(value("\\E f \\in [1..4 -> 1..17] : f[1] = 17 /\\ f[4] = 17"), "TRUE");
    assert_eq!(value("\\A p \\in (1..300) \\X (1..300) : p[1] + p[2] > 1"), "TRUE");
    assert_eq!(value("\\A r \\in [a : 1..300, b : 1..300] : r.a # r.b"), "FALSE");
    assert_eq!(value("\\E s \\in SUBSET (1..17) : s = 1..17"), "TRUE");
    // The first variable varies fastest, so each step of the second one starts it over.
    assert_eq!(value("\\E x, y \\in SUBSET (1..17) : y = {1} /\\ x = {2, 3}"), "TRUE");
    assert_eq!(
        value("{<<x, y>> \\in (1..300) \\X (1..300) : x * y = 300 /\\ x < 4}"),
        "{<<1, 300>>, <<2, 150>>, <<3, 100>>}"
    );
}
