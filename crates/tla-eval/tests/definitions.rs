//! Definitions: recursion, operator arguments, `LAMBDA`, instances, and constants.

mod common;

use std::sync::Arc;

use common::{error, eval, evaluator_with, ints, lookup, show, spec};
use tla_eval::{ConstBinding, Evaluator};

#[test]
fn calls_recursive_operators() {
    let printed = show(
        r#"
RECURSIVE Subsets(_)
Subsets(S) == IF S = {} THEN {{}}
              ELSE LET x == CHOOSE y \in S : TRUE
                       rest == Subsets(S \ {x})
                   IN rest \cup {T \cup {x} : T \in rest}
RECURSIVE IsEven(_), IsOdd(_)
IsEven(S) == IF S = {} THEN TRUE ELSE IsOdd(S \ {CHOOSE x \in S : TRUE})
IsOdd(S) == IF S = {} THEN FALSE ELSE IsEven(S \ {CHOOSE x \in S : TRUE})
Same == Subsets({1, 2, 3}) = SUBSET {1, 2, 3}
Parity == <<IsEven({1, 2, 3}), IsOdd({1, 2, 3}), IsEven({})>>
"#,
        &["Same", "Parity"],
    );
    assert_eq!(printed, ["TRUE", "<<FALSE, TRUE, TRUE>>"]);
}

#[test]
fn applies_recursive_functions_lazily() {
    let printed = show(
        r#"
Subsets[S \in SUBSET {1, 2, 3}] ==
    IF S = {} THEN {{}}
    ELSE LET x == CHOOSE y \in S : TRUE
         IN Subsets[S \ {x}] \cup {T \cup {x} : T \in Subsets[S \ {x}]}
Nest[S \in SUBSET STRING] == IF S = {} THEN <<>> ELSE <<Nest[S \ {CHOOSE x \in S : TRUE}]>>
Same == Subsets[{1, 2, 3}] = SUBSET {1, 2, 3}
Nested == Nest[{"p", "q"}]
Chain == LET f[S \in SUBSET {1, 2}] == IF S = {} THEN {} ELSE f[S \ {CHOOSE x \in S : TRUE}] \cup {S}
         IN f[{1, 2}]
Table == LET g[x \in {1, 2}] == {x} IN g
"#,
        &["Same", "Nested", "Chain", "Table"],
    );
    assert_eq!(printed, ["TRUE", "<<<<<<>>>>>>", "{{2}, {1, 2}}", "<<{1}, {2}>>"]);
}

/// Evaluation recurses on the Rust stack, so a checker runs it on a thread with a large one, as
/// TLC runs on a JVM with a large stack.
#[test]
fn recurses_hundreds_of_calls_deep() {
    let printed = std::thread::Builder::new()
        .stack_size(16 << 20)
        .spawn(|| {
            show(
                r#"
RECURSIVE Depth(_)
Depth(S) == IF S = {} THEN <<>> ELSE LET rest == Depth(S \ {CHOOSE x \in S : TRUE}) IN rest
Big == {s : s \in SUBSET {1, 2, 3, 4, 5, 6, 7, 8}}
Expr == Depth(Big)
"#,
                &["Expr"],
            )
        })
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(printed, ["<<>>"]);
}

#[test]
fn passes_operators_and_lambdas() {
    let printed = show(
        r#"
Apply(F(_), v) == F(v)
Twice(F(_), v) == Apply(F, Apply(F, v))
Wrap(x) == <<x>>
Combine(F(_, _), a, b) == F(a, b)
WithParam(p) == Apply(LAMBDA x : <<x, p>>, 1)
Nested(p) == LET Inner(q) == Twice(LAMBDA x : <<x, p, q>>, 0) IN Inner(5)
Named == Apply(Wrap, 1)
Lambda == Twice(LAMBDA x : {x}, 2)
Captured == WithParam(7)
Deep == Nested(3)
Builtins == <<Combine(\cup, {1}, {2}), Combine(=, 1, 1), Combine(\in, 1, {2})>>
Higher(G(_, _)) == G({1}, {1, 3})
Passed == Higher(\subseteq)
"#,
        &["Named", "Lambda", "Captured", "Deep", "Builtins", "Passed"],
    );
    assert_eq!(
        printed,
        ["<<1>>", "{{2}}", "<<1, 7>>", "<<<<0, 3, 5>>, 3, 5>>", "<<{1, 2}, TRUE, FALSE>>", "TRUE"]
    );
}

#[test]
fn evaluates_arguments_only_where_read() {
    let printed = show(
        r#"
First(a, b) == a
Fails == CHOOSE x \in {} : TRUE
Unused == First(1, Fails)
Applied == [x \in {1, 2} |-> IF x = 1 THEN 0 ELSE Fails][1]
Called(f) == f[1]
Passed == Called([x \in {1, 2} |-> IF x = 1 THEN 0 ELSE Fails])
"#,
        &["Unused", "Applied", "Passed"],
    );
    assert_eq!(printed, ["1", "0", "0"]);
}

#[test]
fn keeps_what_a_lazy_value_captured() {
    let printed = show(
        r#"
Filters == [x \in {"u", "v"} |-> {y \in STRING : y = x}]
Count == \A x \in {"u", "v"} : x \in Filters[x] /\ \A y \in {"u", "v"} \ {x} : y \notin Filters[x]
Functions == [x \in {1, 2} |-> [s \in STRING |-> <<s, x>>]]
Applied == <<Functions[1]["k"], Functions[2]["k"]>>
"#,
        &["Count", "Applied"],
    );
    assert_eq!(printed, ["TRUE", "<<<<\"k\", 1>>, <<\"k\", 2>>>>"]);
}

const INNER: &str = r#"
---- MODULE Inner ----
CONSTANT C, F(_)
Get == F(C)
Pair(x) == <<C, x>>
====
"#;

#[test]
fn instantiates_modules_with_substitutions() {
    let evaluator = evaluator_with(
        r#"
Wrap(x) == {x}
I == INSTANCE Inner WITH C <- 1, F <- LAMBDA x : <<x>>
P(c) == INSTANCE Inner WITH C <- c, F <- Wrap
Named == I!Get
Parameterized == <<P(5)!Get, P({6})!Pair(7)>>
InLet(c) == LET J == INSTANCE Inner WITH C <- c, F <- LAMBDA x : <<x, c>> IN J!Get
Local == InLet(8)
"#,
        &[("Inner", INNER)],
        Vec::new(),
    );
    let printed: Vec<String> = ["Named", "Parameterized", "Local"]
        .iter()
        .map(|name| eval(&evaluator, name).unwrap().to_string())
        .collect();
    assert_eq!(printed, ["<<1>>", "<<{5}, <<{6}, 7>>>>", "<<8, 8>>"]);
}

#[test]
fn instantiates_unnamed_instances() {
    let evaluator = evaluator_with(
        "Wrap(x) == {x}\nINSTANCE Inner WITH C <- 2, F <- Wrap\nExpr == Pair(Get)",
        &[("Inner", INNER)],
        Vec::new(),
    );
    assert_eq!(eval(&evaluator, "Expr").unwrap().to_string(), "<<2, {2}>>");
}

#[test]
fn reads_constants_from_the_model() {
    let spec =
        spec("CONSTANT N, G(_)\nDouble(x) == <<x, x>>\nExpr == G(N)\nSet == N \\cup {0}", &[]);
    let double = lookup(&spec, "Double");
    let constants = vec![ConstBinding::Value(ints(&[1, 2])), ConstBinding::Def(double)];
    let evaluator = Evaluator::new(Arc::new(spec), constants);
    assert_eq!(eval(&evaluator, "Expr").unwrap().to_string(), "<<{1, 2}, {1, 2}>>");
    assert_eq!(eval(&evaluator, "Set").unwrap().to_string(), "{0, 1, 2}");
    let valued = evaluator_with(
        "CONSTANT F(_)\nApply(G(_)) == G(2)\nExpr == <<F(1), Apply(F)>>",
        &[],
        vec![ConstBinding::Value(ints(&[7]))],
    );
    assert_eq!(eval(&valued, "Expr").unwrap().to_string(), "<<{7}, {7}>>");
    let unbound = evaluator_with("CONSTANT N\nExpr == N", &[], Vec::new());
    assert_eq!(
        eval(&unbound, "Expr").unwrap_err().message,
        "The constant parameter N is not assigned a value by the configuration file."
    );
}

#[test]
fn fails_on_arguments_only_when_used() {
    assert_eq!(
        error("LET First(a, b) == b IN First(1, CHOOSE x \\in {} : TRUE)").message,
        "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P."
    );
}

/// tla-ts's `Capture` and `Binders` fixtures: a substitution keeps referring to the names it
/// was written among, whatever the instantiated module binds.
#[test]
fn substitutes_without_capturing_names() {
    let capture = r#"
---- MODULE CaptureInner ----
CONSTANT C
Has(S) == \E p \in S : p = C
====
"#;
    let binders = r#"
---- MODULE BindersInner ----
CONSTANT c, Combine(_, _)
Combined == \E i \in {0, 1} : Combine(i, c) = <<1, c, c>>
Named == \E Lambda \in {0, 1} : Combine(Lambda, c) = <<1, c, c>>
====
"#;
    let evaluator = evaluator_with(
        r#"
I(p) == INSTANCE CaptureInner WITH C <- p
P(i) == INSTANCE BindersInner WITH c <- i, Combine <- LAMBDA a, b : <<a, b, i>>
Captured == <<I(3)!Has({1, 3}), I(3)!Has({1, 2})>>
Bound == <<P(5)!Combined, P(5)!Named, \A i \in {6, 7} : P(i)!Named>>
"#,
        &[("CaptureInner", capture), ("BindersInner", binders)],
        Vec::new(),
    );
    assert_eq!(eval(&evaluator, "Captured").unwrap().to_string(), "<<TRUE, FALSE>>");
    assert_eq!(eval(&evaluator, "Bound").unwrap().to_string(), "<<TRUE, TRUE, TRUE>>");
}

/// tla-ts's `Symbols` fixture, with set operators for arithmetic: built-in operators substituted
/// for constant operators, applied directly and passed on.
#[test]
fn substitutes_built_in_operators() {
    let inner = r#"
---- MODULE SymbolsInner ----
CONSTANT Op(_, _), Neg(_)
Twice(F(_, _), a) == F(a, a)
Applied == Op({1, 2}, {2, 3})
Passed == Twice(Op, {4})
Negated == Neg(<<5>>)
PassedNeg == LET G(H(_)) == H(<<1, 1>>) IN G(Neg)
====
"#;
    let evaluator = evaluator_with(
        r#"
Union == INSTANCE SymbolsInner WITH Neg <- DOMAIN, Op <- \cup
Difference(a) == INSTANCE SymbolsInner WITH Neg <- DOMAIN, Op <- \
INSTANCE SymbolsInner WITH Neg <- SUBSET, Op <- \cap
Unioned == <<Union!Applied, Union!Passed, Union!Negated, Union!PassedNeg>>
Differed == <<Difference(1)!Applied, Difference(1)!Passed>>
Direct == <<Applied, Negated>>
InLet == LET Sum == INSTANCE SymbolsInner WITH Neg <- DOMAIN, Op <- \cup IN Sum!Passed
"#,
        &[("SymbolsInner", inner)],
        Vec::new(),
    );
    let printed: Vec<String> = ["Unioned", "Differed", "Direct", "InLet"]
        .iter()
        .map(|name| eval(&evaluator, name).unwrap().to_string())
        .collect();
    assert_eq!(
        printed,
        ["<<{1, 2, 3}, {4}, 1..1, 1..2>>", "<<{1}, {}>>", "<<{2}, SUBSET <<5>>>>", "{4}"]
    );
}

/// tla-ts's `Scoping` fixture: recursive operators and functions of an instantiated module.
#[test]
fn recurses_inside_instances() {
    let counter = r#"
---- MODULE ScopingCounter ----
CONSTANT Limit
RECURSIVE Chain(_)
Chain(S) == IF S = {} THEN {} ELSE LET rest == Chain(S \ {CHOOSE x \in S : TRUE}) IN rest \cup {S}
Table[S \in SUBSET Limit] == IF S = {} THEN <<>> ELSE <<Table[S \ {CHOOSE x \in S : TRUE}]>>
====
"#;
    let evaluator = evaluator_with(
        r#"
Bounded == INSTANCE ScopingCounter WITH Limit <- {1, 2}
B(l) == INSTANCE ScopingCounter WITH Limit <- l
Named == <<Bounded!Chain({1, 2}), Bounded!Table[{1, 2}]>>
Parameterized == <<B({1, 2, 3})!Table[{3}], B({4})!Table>>
"#,
        &[("ScopingCounter", counter)],
        Vec::new(),
    );
    assert_eq!(eval(&evaluator, "Named").unwrap().to_string(), "<<{{2}, {1, 2}}, <<<<<<>>>>>>>>");
    assert_eq!(
        eval(&evaluator, "Parameterized").unwrap().to_string(),
        "<<<<<<>>>>, ({} :> <<>> @@ {4} :> <<<<>>>>)>>"
    );
}

/// TLC enumerates a function over a set enumeration or an interval at once, and builds one over
/// any other domain lazily, so that its body fails only at the arguments it is applied to.
#[test]
fn defers_errors_of_functions_over_other_domains() {
    let product = "[x \\in {1, 2}, y \\in {3} |-> IF x = 1 THEN 0 ELSE CHOOSE z \\in {} : TRUE]";
    let subsets = "[s \\in SUBSET {1} |-> IF s = {} THEN 0 ELSE CHOOSE z \\in {} : TRUE]";
    let printed = show(
        &format!(
            "Product == \\E f \\in {{{product}}} : f[1, 3] = 0\nSubsets == \\E f \\in {{{subsets}}} : f[{{}}] = 0"
        ),
        &["Product", "Subsets"],
    );
    assert_eq!(printed, ["TRUE", "TRUE"]);
    assert_eq!(
        error(
            "\\E f \\in {[x \\in {1, 2} |-> IF x = 1 THEN 0 ELSE CHOOSE z \\in {} : TRUE]} : TRUE"
        )
        .message,
        "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P."
    );
}

#[test]
fn shares_evaluators_across_threads() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<Evaluator>();
    assert_send_sync::<tla_eval::Value>();
}
