//! Constant expressions built from TLA+'s own operators, compared with TLC's printed values.

mod common;

use common::{evaluator, show, value};
use tla_eval::Value;

#[test]
fn evaluates_literals_and_tuples() {
    assert_eq!(value("TRUE"), "TRUE");
    assert_eq!(value("42"), "42");
    assert_eq!(value("\"line\\none\""), "\"line\\none\"");
    assert_eq!(value("<<1, TRUE, <<>>>>"), "<<1, TRUE, <<>>>>");
}

#[test]
fn builds_sets_in_tlc_order() {
    assert_eq!(value("{3, 1, 2, 1}"), "{1, 2, 3}");
    assert_eq!(value("{}"), "{}");
    assert_eq!(value("{{2, 1}, {1}, {}}"), "{{}, {1}, {1, 2}}");
    assert_eq!(value("BOOLEAN"), "{FALSE, TRUE}");
    assert_eq!(value("{1, 2} \\cup {2, 3}"), "{1, 2, 3}");
    assert_eq!(value("{1, 2, 3} \\cap {2, 3, 4}"), "{2, 3}");
    assert_eq!(value("{1, 2, 3} \\ {2}"), "{1, 3}");
    assert_eq!(value("UNION {{1}, {2, 3}, {}}"), "{1, 2, 3}");
    assert_eq!(value("SUBSET {1, 2}"), "{{}, {1}, {2}, {1, 2}}");
    assert_eq!(value("{1, 2} \\X {3}"), "{<<1, 3>>, <<2, 3>>}");
    assert_eq!(
        value("[{1, 2} -> {TRUE, FALSE}]"),
        "{<<FALSE, FALSE>>, <<FALSE, TRUE>>, <<TRUE, FALSE>>, <<TRUE, TRUE>>}"
    );
}

#[test]
fn tests_membership_and_subsets() {
    assert_eq!(value("2 \\in {1, 2}"), "TRUE");
    assert_eq!(value("3 \\notin {1, 2}"), "TRUE");
    assert_eq!(value("{1} \\subseteq {1, 2} /\\ ~({3} \\subseteq {1, 2})"), "TRUE");
    assert_eq!(value("{1, 3} \\in SUBSET {1, 2, 3}"), "TRUE");
    assert_eq!(value("<<1, TRUE>> \\in {1} \\X BOOLEAN"), "TRUE");
    assert_eq!(value("\"x\" \\in STRING /\\ {\"x\", \"y\"} \\in SUBSET STRING"), "TRUE");
    assert_eq!(value("<<1, 2>> \\in [{1, 2} -> {1, 2}]"), "TRUE");
}

#[test]
fn evaluates_boolean_operators() {
    assert_eq!(value("(TRUE => FALSE) = FALSE /\\ (FALSE => FALSE)"), "TRUE");
    assert_eq!(value("(TRUE <=> TRUE) /\\ ~(TRUE <=> FALSE)"), "TRUE");
    assert_eq!(value("TRUE \\/ (1 = \"a\")"), "TRUE");
    assert_eq!(value("FALSE /\\ (1 = \"a\")"), "FALSE");
    assert_eq!(value("FALSE => (1 = \"a\")"), "TRUE");
    assert_eq!(value("/\\ TRUE\n         /\\ \\/ FALSE\n            \\/ TRUE"), "TRUE");
}

#[test]
fn chooses_conditionals_and_cases() {
    assert_eq!(value("IF {} = {} THEN 1 ELSE 2"), "1");
    assert_eq!(value("CASE FALSE -> 1 [] TRUE -> 2 [] TRUE -> 3"), "2");
    assert_eq!(value("CASE FALSE -> 1 [] OTHER -> 3"), "3");
}

#[test]
fn quantifies_over_bounded_sets() {
    assert_eq!(value("\\A x \\in {1, 2} : x \\in {1, 2, 3}"), "TRUE");
    assert_eq!(value("\\E x \\in {} : TRUE"), "FALSE");
    assert_eq!(value("\\A x \\in {} : FALSE"), "TRUE");
    assert_eq!(value("\\E <<x, y>> \\in {<<1, 2>>, <<3, 4>>} : y = 4 /\\ x = 3"), "TRUE");
    assert_eq!(value("\\A x, y \\in {1, 2} : {x, y} \\subseteq {1, 2}"), "TRUE");
    assert_eq!(value("\\E x \\in {1, 2}, y \\in {3} : <<x, y>> = <<2, 3>>"), "TRUE");
    assert_eq!(value("\\E x \\in {1} : \\E y \\in {x} : y = 1"), "TRUE");
}

#[test]
fn chooses_the_first_element_in_tlc_order() {
    assert_eq!(value("CHOOSE x \\in {3, 1, 2} : TRUE"), "1");
    assert_eq!(value("CHOOSE x \\in {3, 1, 2} : x # 1"), "2");
    assert_eq!(value("CHOOSE s \\in SUBSET {1, 2} : s # {}"), "{1}");
    assert_eq!(value("CHOOSE s \\in {{1, 2}, {3}} : TRUE"), "{3}");
    assert_eq!(value("CHOOSE <<x, y>> \\in {<<2, 1>>, <<1, 2>>} : x # 1"), "<<2, 1>>");
}

#[test]
fn builds_set_comprehensions() {
    assert_eq!(value("{x \\in {1, 2, 3} : x # 2}"), "{1, 3}");
    assert_eq!(value("{{x} : x \\in {1, 2}}"), "{{1}, {2}}");
    assert_eq!(value("{<<x, y>> : x \\in {1, 2}, y \\in {TRUE}}"), "{<<1, TRUE>>, <<2, TRUE>>}");
    assert_eq!(value("{x : x \\in {1, 1, 1}}"), "{1}");
    assert_eq!(value("{s \\in SUBSET {1, 2} : s # {}}"), "{{1}, {2}, {1, 2}}");
    assert_eq!(value("{<<x, y>> \\in {1, 2} \\X {3} : x = 2}"), "{<<2, 3>>}");
    assert_eq!(value("\"b\" \\in {s \\in STRING : s # \"a\"}"), "TRUE");
    assert_eq!(value("\"a\" \\in {s \\in STRING : s # \"a\"}"), "FALSE");
}

#[test]
fn builds_and_applies_functions() {
    assert_eq!(value("[x \\in {1, 2} |-> {x}]"), "<<{1}, {2}>>");
    assert_eq!(value("[x \\in {2, 3} |-> {x}]"), "(2 :> {2} @@ 3 :> {3})");
    assert_eq!(value("[x \\in {} |-> 0]"), "<<>>");
    assert_eq!(value("[x \\in {1, 2} |-> {x}][2]"), "{2}");
    assert_eq!(value("[x \\in {1, 2}, y \\in {3} |-> <<x, y>>][2, 3]"), "<<2, 3>>");
    assert_eq!(value("[x, y \\in {1, 2} |-> {x, y}][1, 2]"), "{1, 2}");
    assert_eq!(value("[<<x, y>> \\in {<<1, 2>>} |-> {x, y}][<<1, 2>>]"), "{1, 2}");
    assert_eq!(value("[x \\in {1}, y \\in {2} |-> x]"), "(<<1, 2>> :> 1)");
    assert_eq!(value("DOMAIN <<TRUE, FALSE>>"), "1..2");
    assert_eq!(value("DOMAIN [x \\in {2, 3} |-> x]"), "{2, 3}");
    assert_eq!(value("[s \\in STRING |-> <<s>>][\"q\"]"), "<<\"q\">>");
}

#[test]
fn builds_records_and_sets_of_records() {
    assert_eq!(value("[first |-> 1, second |-> 2].second"), "2");
    assert_eq!(value("[first |-> 1, second |-> 2] = [second |-> 2, first |-> 1]"), "TRUE");
    assert_eq!(
        value(
            "[kind : {\"a\", \"b\"}, size : {1}] = {[kind |-> \"a\", size |-> 1], [kind |-> \"b\", size |-> 1]}"
        ),
        "TRUE"
    );
    assert_eq!(value("[a |-> 1] \\in [a : {1, 2}]"), "TRUE");
    assert_eq!(value("[a |-> 3] \\in [a : {1, 2}]"), "FALSE");
}

#[test]
fn updates_functions_with_except() {
    assert_eq!(value("[<<1, 2, 3>> EXCEPT ![2] = 20]"), "<<1, 20, 3>>");
    assert_eq!(value("[<<{1}, {2}>> EXCEPT ![1] = @ \\cup {3}]"), "<<{1, 3}, {2}>>");
    assert_eq!(
        value("[<<<<1>>, <<2>>>> EXCEPT ![2] = [@ EXCEPT ![1] = {@}]]"),
        "<<<<1>>, <<{2}>>>>"
    );
    assert_eq!(value("[[a |-> <<1, 2>>] EXCEPT !.a[1] = 9] = [a |-> <<9, 2>>]"), "TRUE");
    assert_eq!(value("[[a |-> 1, b |-> 2] EXCEPT !.a = 3, !.b = @] = [a |-> 3, b |-> 2]"), "TRUE");
    assert_eq!(value("[<<1, 2>> EXCEPT ![1] = 5, ![1] = {@}]"), "<<{5}, 2>>");
    assert_eq!(value("[<<1, 2>> EXCEPT ![3] = 5]"), "<<1, 2>>");
    assert_eq!(value("[[x \\in {1, 2}, y \\in {3} |-> 0] EXCEPT ![2, 3] = 1][2, 3]"), "1");
    assert_eq!(value("[[s \\in STRING |-> 0] EXCEPT ![\"k\"] = 1][\"k\"]"), "1");
}

#[test]
fn binds_let_definitions() {
    assert_eq!(value("LET a == {1}\n         b(x) == x \\cup a\n     IN b({2})"), "{1, 2}");
    let printed = show(
        "Op(p) == LET q == {p}\n              r(s) == q \\cup s\n          IN LET t == r({9}) IN <<t, p>>\nExpr == Op(4)",
        &["Expr"],
    );
    assert_eq!(printed, ["<<{4, 9}, 4>>"]);
}

/// The assumptions of tla-ts's `Semantics` fixture that use only TLA+'s own operators.
#[test]
fn holds_the_semantics_assumptions() {
    let evaluator = evaluator(
        r#"
ASSUME {1} \subseteq {1, 2} /\ ~({3} \subseteq {1, 2})
ASSUME SUBSET {1, 2} = {{}, {1}, {2}, {1, 2}}
ASSUME UNION {{1}, {2, 3}} = {1, 2, 3}
ASSUME ~\E x \in {} : TRUE
ASSUME \E <<x, y>> \in {1, 2} \X {1, 2} : x = 2 /\ y = 2
ASSUME IF TRUE THEN TRUE ELSE FALSE
ASSUME CASE FALSE -> FALSE [] TRUE -> TRUE [] OTHER -> FALSE
ASSUME (CASE FALSE -> 1 [] OTHER -> 2) = 2
ASSUME LET double(n) == <<n, n>>
           pair == double(2)
       IN pair = <<2, 2>>
ASSUME [x \in {1, 2, 3} |-> {x}][2] = {2}
ASSUME DOMAIN [x \in {"a", "b"} |-> 0] = {"a", "b"}
ASSUME [x \in {1, 2} |-> x] = <<1, 2>>
ASSUME [first |-> 1, second |-> 2].second = 2
ASSUME [first |-> 1, second |-> 2] = [second |-> 2, first |-> 1]
ASSUME [<<1, 2, 3>> EXCEPT ![2] = 20] = <<1, 20, 3>>
ASSUME [[a |-> <<1, 2>>] EXCEPT !.a[1] = 9] = [a |-> <<9, 2>>]
ASSUME [[a |-> 1, b |-> 2] EXCEPT !.a = 3, !.b = 4] = [a |-> 3, b |-> 4]
ASSUME [{1, 2} -> {"a"}] = {<<"a", "a">>}
ASSUME [kind : {"a", "b"}, size : {1}] = {[kind |-> "a", size |-> 1], [kind |-> "b", size |-> 1]}
ASSUME [a |-> 1] \in [a : {1}]
ASSUME "abc" = "abc" /\ "abc" # "abd"
ASSUME {"b", "a"} = {"a", "b"}
ASSUME BOOLEAN = {TRUE, FALSE}
ASSUME (TRUE => FALSE) = FALSE /\ (FALSE => FALSE)
ASSUME (TRUE <=> TRUE) /\ ~(TRUE <=> FALSE)
ASSUME {{1, 2}, {2, 1}} = {{1, 2}}
ASSUME <<>> = [x \in {} |-> 0]
ASSUME (CHOOSE s \in {{1}, {2, 3}} : TRUE) = {1}
ASSUME {<<x, y>> : x \in {1, 2}, y \in {"a"}} = {<<1, "a">>, <<2, "a">>}

Shadow(Later) == Later[1]
Later == [n \in {1, 2} |-> 0]
ASSUME Shadow([n \in {1, 2} |-> {n}]) = {1}

Apply(F(_), value) == F(value)
Singleton(n) == {n}
ASSUME Apply(Singleton, 1) = {1}
ASSUME Apply(LAMBDA n : <<n>>, 2) = <<2>>

a (+) b == {a, b}
ASSUME 1 (+) 2 = {1, 2}
"#,
    );
    let spec = evaluator.spec();
    assert_eq!(spec.assumptions.len(), 33);
    for &assumption in &spec.assumptions {
        let value = evaluator.eval_def(assumption, None);
        let def = spec.def(assumption);
        let line = def.span.line_column(&spec.modules[def.module.index()].source).0;
        assert!(matches!(value, Ok(Value::Bool(true))), "line {line}: {value:?}");
    }
}
