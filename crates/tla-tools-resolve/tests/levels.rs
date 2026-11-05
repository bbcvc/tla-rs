//! SANY's level checking: the levels of definitions, and the level errors SANY reports. Many
//! cases come from tla-ts, which checked them against SANY.

use std::collections::HashMap;

use tla_tools_resolve::{DefId, Level, ResolveError, RootName, Spec, resolve};

fn resolve_with(root: &str, modules: &[(&str, &str)]) -> Result<Spec, ResolveError> {
    let modules: HashMap<String, String> =
        modules.iter().map(|(name, source)| (name.to_string(), source.to_string())).collect();
    resolve(root, &mut |name: &str| modules.get(name).cloned())
}

fn spec(root: &str, modules: &[(&str, &str)]) -> Spec {
    resolve_with(root, modules).unwrap_or_else(|error| panic!("{error}"))
}

fn error(root: &str, modules: &[(&str, &str)]) -> ResolveError {
    resolve_with(root, modules).expect_err("level checking should fail")
}

fn def(spec: &Spec, name: &str) -> DefId {
    match spec.lookup(name) {
        Some(RootName::Def(id)) => id,
        other => panic!("{name} is {other:?}"),
    }
}

fn level(spec: &Spec, name: &str) -> Level {
    spec.level(def(spec, name))
}

use Level::{Action, Constant, State, Temporal};

const COUNTER: &str = r#"
---- MODULE Counter ----
EXTENDS Naturals, Sequences
CONSTANT N
VARIABLE x
vars == <<x>>
TypeOK == x \in 0..N
Init == x = 0
Next == x < N /\ x' = x + 1
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Live == <>(x = N)
Max == N + 1
Enabled == ENABLED Next
Changed == ~UNCHANGED x
Inc(v) == v + 1
Prime(v) == v'
Always(P) == []P
Twice(F(_), v) == F(F(v))
Local == LET a == x' IN a = 1
====
"#;

#[test]
fn computes_the_levels_of_typical_definitions() {
    let spec = spec(COUNTER, &[]);
    let levels = ["TypeOK", "Init", "Next", "Spec", "Live", "Max", "Enabled", "Changed", "Local"]
        .map(|name| level(&spec, name));
    assert_eq!(levels, [State, State, Action, Temporal, Temporal, Constant, State, Action, Action]);
}

#[test]
fn computes_what_each_parameter_allows() {
    let spec = spec(COUNTER, &[]);
    let inc = spec.def_levels(def(&spec, "Inc"));
    assert_eq!((inc.level, &inc.max_levels, &inc.weights), (Constant, &vec![Action], &vec![true]));
    assert_eq!(inc.applied(&[State]), State);
    assert_eq!(inc.leibniz, [true]);

    let prime = spec.def_levels(def(&spec, "Prime"));
    assert_eq!(
        (prime.level, &prime.max_levels, &prime.weights),
        (Action, &vec![State], &vec![false])
    );
    assert_eq!(prime.applied(&[State]), Action);
    assert_eq!(prime.leibniz, [false]);

    let always = spec.def_levels(def(&spec, "Always"));
    assert_eq!((always.level, &always.max_levels), (Temporal, &vec![Temporal]));

    let twice = spec.def_levels(def(&spec, "Twice"));
    assert_eq!(twice.min_max_levels, [vec![Constant], vec![]]);
}

#[test]
fn computes_the_levels_sany_computes_for_the_standard_modules() {
    // tla-ts records what SANY computes for these: parameter arities, maximum levels, weights.
    let spec = spec("---- MODULE M ----\nEXTENDS Sequences, TLC, Bags, FiniteSets\n====", &[]);
    let cases: &[(&str, &[Level], &[bool])] = &[
        ("SelectSeq", &[Action, Action], &[true, true]),
        ("SortSeq", &[Action, Action], &[true, true]),
        ("Print", &[Temporal, Temporal], &[false, true]),
        ("PrintT", &[Temporal], &[false]),
        ("Assert", &[Action, Temporal], &[true, false]),
        ("TLCGet", &[Temporal], &[false]),
        ("TLCSet", &[Temporal, Temporal], &[false, false]),
        (":>", &[Action, Temporal], &[true, true]),
        ("@@", &[Action, Action], &[true, true]),
        ("RandomElement", &[Temporal], &[true]),
        ("TLCEval", &[Temporal], &[true]),
        ("SetToBag", &[Temporal], &[true]),
        ("BagOfAll", &[Action, Action], &[true, true]),
        ("Cardinality", &[Action], &[true]),
        ("Append", &[Action, Action], &[true, true]),
    ];
    for (name, max_levels, weights) in cases {
        let levels = spec.def_levels(def(&spec, name));
        assert_eq!(levels.level, Constant, "{name}");
        assert_eq!(levels.max_levels, *max_levels, "{name}");
        assert_eq!(levels.weights, *weights, "{name}");
    }
}

#[test]
fn bounds_an_operator_argument_by_the_arguments_passed_to_it() {
    // SANY bounds a sequence argument by the level its LAMBDA allows for the elements.
    for application in [
        "SelectSeq(s, LAMBDA a : a' = 1)",
        "SortSeq(s, LAMBDA a, b : a' = b)",
        "SortSeq(s, LAMBDA a, b : a = b')",
    ] {
        let source = format!(
            "---- MODULE M ----\nEXTENDS Sequences, TLC\nVARIABLE x\nF(s) == {application}\nG == F(x')\n===="
        );
        let found = error(&source, &[]);
        assert_eq!(
            found.message,
            "Level error in applying operator F:\nThe level of argument 1 exceeds the maximum level allowed by the operator.",
            "{application}"
        );
        assert_eq!((found.line, found.column), (5, 6), "{application}");
    }
}

#[test]
fn checks_operator_arguments_against_what_the_operator_requires_of_them() {
    let source = |definition: &str| {
        format!(
            "---- MODULE M ----\nVARIABLE x\nF(G(_)) == G(x')\nAp(G(_), v) == G(v)\n{definition}\n===="
        )
    };
    let spec = spec(&source("Ok == F(LAMBDA a : a = 1)"), &[]);
    assert_eq!(spec.def_levels(def(&spec, "F")).min_max_levels, [vec![Action]]);
    assert_eq!(
        error(&source("Bad == F(LAMBDA a : a' = 1)"), &[]).message,
        "Level error in applying operator F:\nThe permitted level of argument 1 of the operator argument 1 \nmust be at least 2."
    );
    assert_eq!(
        error(&source("Bad == Ap(LAMBDA a : a' = 1, x')"), &[]).message,
        "Level error in applying operator Ap:\nThe level of argument 2 exceeds the maximum level allowed by the operator."
    );
}

fn check_definition(definition: &str) -> Result<Spec, ResolveError> {
    let source = format!("---- MODULE M ----\nVARIABLE x\nF == {definition}\n====");
    resolve_with(&source, &[])
}

#[test]
fn rejects_raw_actions_in_temporal_formulas() {
    // From SANY's test215, which outlaws raw actions in temporal formulas.
    for (definition, message) in [
        ("x' ~> []x", "Action used where only temporal formula or state predicate allowed."),
        ("[]x -+-> x'", "Action used where only temporal formula or state predicate allowed."),
        ("<>(x')", "<> followed by action not of form <<A>>_v."),
        ("[](x')", "[] followed by action not of form [A]_v."),
        ("\\A i \\in {}, j \\in x' : []x", "Action-level bound of quantified temporal formula."),
        ("x' /\\ []x", "\\land has both temporal formula and action as arguments."),
        (
            "\n  /\\ x'\n  /\\ []x",
            "Conjunction list has both temporal formula and action as arguments.",
        ),
        ("[]x => x'", "=> has both temporal formula and action as arguments."),
        (
            "(x')'",
            "Level error in applying operator ':\nThe level of argument 1 exceeds the maximum level allowed by the operator.",
        ),
        (
            "UNCHANGED (x')",
            "Level error in applying operator UNCHANGED:\nThe level of argument 1 exceeds the maximum level allowed by the operator.",
        ),
        (
            "ENABLED []x",
            "Level error in applying operator ENABLED:\nThe level of argument 1 exceeds the maximum level allowed by the operator.",
        ),
        (
            "[][x']_(x')",
            "Level error in applying operator $SquareAct:\nThe level of argument 2 exceeds the maximum level allowed by the operator.",
        ),
        (
            "\\E i \\in [](x = 1) : TRUE",
            "Level error in applying operator $BoundedExists:\nThe level of the range for a bounded variable exceeds the maximum level allowed by the operator.",
        ),
    ] {
        let found = check_definition(definition).expect_err(definition);
        assert_eq!(found.message, message, "{definition}");
    }
}

#[test]
fn accepts_what_sany_accepts_in_temporal_formulas() {
    for definition in [
        "x ~> []x",
        "<><<x'>>_x",
        "[][x']_x",
        "\\A i \\in x' : x'",
        "[](LET A == x' IN A)",
        "WF_x(x' = 1) /\\ SF_x(x' = 2)",
        "\\EE y : [](y = x)",
        "ENABLED (x' = 1) ~> []x",
    ] {
        check_definition(definition).unwrap_or_else(|error| panic!("{definition}: {error}"));
    }
}

#[test]
fn reports_the_first_error_where_sany_does() {
    let source = "---- MODULE M ----\nVARIABLE x\nb == x' ~> []x\nh == <>(x')\nn == \\A i \\in {}, j \\in x' : []x\n====";
    let found = error(source, &[]);
    assert_eq!((found.line, found.column), (3, 6));
    let source = "---- MODULE M ----\nVARIABLE x\nn == \\A i \\in {}, j \\in x' : []x\n====";
    let found = error(source, &[]);
    assert_eq!((found.line, found.column), (3, 25));
}

#[test]
fn rejects_a_primed_argument_of_a_recursive_operator() {
    let source = "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nRECURSIVE R(_)\nR(n) == IF n' = 0 THEN 0 ELSE R(n - 1)\n====";
    assert_eq!(error(source, &[]).message, "Argument 1 of recursive operator R is primed");
}

#[test]
fn levels_a_recursive_section_as_sany_does() {
    let source = r#"
---- MODULE M ----
EXTENDS Naturals
VARIABLE x
RECURSIVE Sum(_), Count(_)
Sum(S) == IF S = {} THEN 0 ELSE x + Sum(S \ {CHOOSE e \in S : TRUE})
Count(S) == IF S = {} THEN 0 ELSE 1 + Count(S \ {CHOOSE e \in S : TRUE})
Total == Count({1, 2})
f[n \in Nat] == IF n = 0 THEN x ELSE f[n - 1]
====
"#;
    let spec = spec(source, &[]);
    let sum = spec.def_levels(def(&spec, "Sum"));
    assert_eq!((sum.level, &sum.max_levels, &sum.weights), (State, &vec![Action], &vec![true]));
    // SANY gives every operator of a section the highest level of any of them.
    assert_eq!(level(&spec, "Count"), State);
    assert_eq!(level(&spec, "Total"), State);
    assert_eq!(level(&spec, "f"), State);

    // A definition made before the section's operators are all defined is in the section, even
    // after an instance of a module with a section of its own.
    let inner = "---- MODULE Inner ----\nEXTENDS Naturals\nRECURSIVE G(_)\nG(n) == IF n = 0 THEN 0 ELSE G(n - 1)\n====";
    let source = "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nRECURSIVE F(_)\nI == INSTANCE Inner\nH == 1\nF(n) == IF n = 0 THEN x ELSE F(n - 1)\nK == 1\n====";
    let sectioned = self::spec(source, &[("Inner", inner)]);
    assert_eq!([level(&sectioned, "H"), level(&sectioned, "K")], [State, Constant]);
}

#[test]
fn requires_assumptions_to_be_constant() {
    let source = "---- MODULE M ----\nVARIABLE x\nASSUME x = 0\n====";
    assert_eq!(
        error(source, &[]).message,
        "Level error: assumptions must be level 0 (Constant), \nbut this one has level 1."
    );
    spec("---- MODULE M ----\nCONSTANT N\nASSUME N = 0\n====", &[]);
}

#[test]
fn levels_instance_definitions_from_their_substituted_bodies() {
    let inner = "---- MODULE Inner ----\nEXTENDS Naturals\nVARIABLE y\nNext == y' = y + 1\nSpec == y = 0 /\\ [][Next]_y\nGet == y\n====";
    let source = "---- MODULE M ----\nVARIABLE x\nI == INSTANCE Inner WITH y <- x\nJ(z) == INSTANCE Inner WITH y <- z\nNext == I!Next\nSpec == I!Spec\nGet == I!Get\nOther == J(x)!Get\nPrimed == J(x')!Get\n====";
    let spec = spec(source, &[("Inner", inner)]);
    let levels = ["Next", "Spec", "Get", "Other", "Primed"].map(|name| level(&spec, name));
    assert_eq!(levels, [Action, Temporal, State, State, Action]);
}

#[test]
fn names_an_operator_of_a_parameterized_instance_like_sany() {
    // SANY's test217.
    let inner = "---- MODULE Inner ----\nVARIABLE y\nTHEOREM Foo == y' = 0\n====";
    let source = "---- MODULE M ----\nVARIABLE x\nI(z) == INSTANCE Inner WITH y <- z\nFooBar == I(x')!Foo\n====";
    let found = error(source, &[("Inner", inner)]);
    assert_eq!(
        found.message,
        "Level error in applying operator I!Foo:\nThe level of argument 1 exceeds the maximum level allowed by the operator."
    );
    assert_eq!((found.module.as_str(), found.line, found.column), ("M", 4, 11));
}

#[test]
fn checks_an_instantiated_module_by_itself() {
    let inner = "---- MODULE Inner ----\nVARIABLE y\nBad == [](y')\n====";
    let source = "---- MODULE M ----\nVARIABLE x\nI == INSTANCE Inner WITH y <- x\n====";
    let found = error(source, &[("Inner", inner)]);
    assert_eq!(found.message, "[] followed by action not of form [A]_v.");
    assert_eq!((found.module.as_str(), found.line), ("Inner", 3));

    // SANY doesn't check the definitions of an instance with the substitutions in place.
    let constant = "---- MODULE Logic ----\nCONSTANT A, B\nBoth == A /\\ B\n====";
    let source =
        "---- MODULE M ----\nVARIABLE x\nI == INSTANCE Logic WITH A <- [](x = 1), B <- x'\n====";
    spec(source, &[("Logic", constant)]);
}

const INNER_MODULES: &[(&str, &str)] = &[
    ("Stateful", "EXTENDS Naturals\nCONSTANT c, Op(_)\nVARIABLE v\nUse == Op(v) + c"),
    ("Pure", "EXTENDS Naturals\nCONSTANT c, Op(_)\nUse == Op(c) + c"),
    ("Primed", "EXTENDS Naturals\nCONSTANT c, Op(_)\nUse == Op(c)' + c"),
    ("Vars", "EXTENDS Naturals\nVARIABLE v, w\nUse == v + w"),
    ("Applied", "CONSTANT c, Op(_)\nUse == Op(c)"),
    ("Assumed", "CONSTANT C, D\nASSUME C = {}\nTHEOREM ASSUME D PROVE TRUE"),
    ("Nested", "EXTENDS Naturals\nCONSTANT c, Op(_)\nVARIABLE v\nUse == Op(v') /\\ c = 1"),
    ("Twice", "CONSTANT c, Op(_, _)\nUse == Op(c, c)\nOther(d) == Op(d, c)"),
    (
        "Outer",
        "EXTENDS Naturals\nCONSTANT c\nN == INSTANCE Twice WITH c <- c, Op <- LAMBDA a, b : a + b\nUse == N!Use",
    ),
    (
        "Functions",
        "EXTENDS Naturals\nCONSTANT c\nf[i \\in {1}] == c + i\nRECURSIVE g(_)\ng(n) == IF n = 0 THEN c ELSE g(n - 1)",
    ),
];

fn check_substitution(body: &str) -> Result<Spec, ResolveError> {
    let modules: Vec<(String, String)> = INNER_MODULES
        .iter()
        .map(|(name, text)| (name.to_string(), format!("---- MODULE {name} ----\n{text}\n====")))
        .collect();
    let modules: Vec<(&str, &str)> =
        modules.iter().map(|(name, text)| (name.as_str(), text.as_str())).collect();
    let source = format!(
        "---- MODULE Main ----\nEXTENDS Naturals\nVARIABLE x\n{body}\nInit == x = 0\nNext == x' = x\n===="
    );
    resolve_with(&source, &modules)
}

fn at_most(module: &str, name: &str, level: u8) -> String {
    format!(
        "Level error in instantiating module '{module}':\nThe level of the expression or operator substituted for '{name}' \nmust be at most {level}."
    )
}

fn non_leibniz(module: &str) -> String {
    format!(
        "Error in instantiating module '{module}':\n A non-Leibniz operator substituted for 'Op'."
    )
}

fn argument_at_most(module: &str, index: usize, maximum: u8) -> String {
    format!(
        "Level error when instantiating module '{module}':\nThe level of the argument {index} of the operator Op' \nmust be at most {maximum}."
    )
}

#[test]
fn rejects_substitutions_above_the_levels_a_module_allows() {
    // tla-ts's cases, with the first error SANY reports for each. tla-ts also rejects
    // `Assumed WITH D <- [](x = 0)` for `THEOREM ASSUME D PROVE TRUE`, which the parser drops.
    let cases = [
        (
            "I == INSTANCE Stateful WITH c <- 1, Op <- LAMBDA a : a + x, v <- x",
            at_most("Stateful", "Op", 0),
        ),
        (
            "I == INSTANCE Stateful WITH c <- x, Op <- LAMBDA a : a, v <- x",
            at_most("Stateful", "c", 0),
        ),
        (
            "I == INSTANCE Stateful WITH c <- x', Op <- LAMBDA a : a, v <- x",
            at_most("Stateful", "c", 0),
        ),
        ("INSTANCE Stateful WITH c <- x, Op <- LAMBDA a : a, v <- x", at_most("Stateful", "c", 0)),
        (
            "F(a) == a + x\nI == INSTANCE Stateful WITH c <- 1, Op <- F, v <- x",
            at_most("Stateful", "Op", 0),
        ),
        ("I == INSTANCE Vars WITH v <- x', w <- x", at_most("Vars", "v", 1)),
        ("I == INSTANCE Vars WITH v <- [](x = 1), w <- x", at_most("Vars", "v", 1)),
        ("I == INSTANCE Primed WITH c <- 1, Op <- LAMBDA a : a + x", at_most("Primed", "Op", 0)),
        ("I == INSTANCE Pure WITH c <- [](x = 1), Op <- LAMBDA a : a", at_most("Pure", "c", 2)),
        ("I == INSTANCE Assumed WITH C <- [](x = 0), D <- TRUE", at_most("Assumed", "C", 2)),
        ("I == INSTANCE Outer WITH c <- [](x = 1)", at_most("Outer", "c", 2)),
        ("I == INSTANCE Functions WITH c <- [](x = 1)", at_most("Functions", "c", 2)),
        (
            "I == INSTANCE Applied WITH c <- [](x = 1), Op <- LAMBDA a : a + 1",
            argument_at_most("Applied", 0, 2),
        ),
        (
            "F(a) == LET G == a' IN G\nI == INSTANCE Applied WITH c <- [](x = 1), Op <- F",
            argument_at_most("Applied", 0, 1),
        ),
        (
            "I == INSTANCE Twice WITH c <- [](x = 1), Op <- LAMBDA a, b : a + b",
            argument_at_most("Twice", 0, 2),
        ),
        (
            "F(a) == LET G == a' IN G\nI == INSTANCE Nested WITH c <- 1, Op <- F, v <- x",
            at_most("Nested", "Op", 0),
        ),
        (
            "Foo == LET I == INSTANCE Stateful WITH c <- x, Op <- LAMBDA a : a, v <- x IN I!Use",
            at_most("Stateful", "c", 0),
        ),
        (
            "Foo == LET k == x\n           I == INSTANCE Stateful WITH c <- k, Op <- LAMBDA a : a, v <- x IN I!Use",
            at_most("Stateful", "c", 0),
        ),
        (
            "Foo == LET k == x\n           j == k + 1\n           I == INSTANCE Stateful WITH c <- j, Op <- LAMBDA a : a, v <- x IN I!Use",
            at_most("Stateful", "c", 0),
        ),
        (
            "Foo == LET F(a) == a + x\n           I == INSTANCE Stateful WITH c <- 1, Op <- F, v <- x IN I!Use",
            at_most("Stateful", "Op", 0),
        ),
        (
            "Foo == LET F(a) == a'\n           I == INSTANCE Pure WITH c <- 1, Op <- F IN I!Use",
            non_leibniz("Pure"),
        ),
        ("F(a) == a'\nI == INSTANCE Pure WITH c <- 1, Op <- F", non_leibniz("Pure")),
        ("I == INSTANCE Pure WITH c <- 1, Op <- LAMBDA a : ENABLED a", non_leibniz("Pure")),
        ("I == INSTANCE Pure WITH c <- 1, Op <- LAMBDA a : UNCHANGED a", non_leibniz("Pure")),
        ("I == INSTANCE Pure WITH c <- 1, Op <- LAMBDA a : [](a = 1)", non_leibniz("Pure")),
        (
            "G(b) == b'\nF(a) == G(a) + 1\nI == INSTANCE Pure WITH c <- 1, Op <- F",
            non_leibniz("Pure"),
        ),
        (
            "a ++ b == a' + b\nF(a) == a ++ 1\nI == INSTANCE Pure WITH c <- 1, Op <- F",
            non_leibniz("Pure"),
        ),
        (
            "F(a) == \\E k \\in {1} : a' = k\nI == INSTANCE Pure WITH c <- 1, Op <- F",
            non_leibniz("Pure"),
        ),
        ("F(a) == [a = 1]_a\nI == INSTANCE Pure WITH c <- 1, Op <- F", non_leibniz("Pure")),
    ];
    for (body, message) in cases {
        let found = check_substitution(body).expect_err(body);
        assert_eq!(found.message, message, "{body}");
    }
}

#[test]
fn reports_a_substitution_error_at_the_whole_instance() {
    let body = "I == INSTANCE Pure WITH c <- 1, Op <- LAMBDA a : ENABLED a";
    let found = check_substitution(body).unwrap_err();
    assert_eq!((found.module.as_str(), found.line, found.column), ("Main", 4, 1));
    assert_eq!(found.span.end - found.span.start, body.len() as u32);
}

#[test]
fn rejects_the_operator_a_constant_operator_argument_needs() {
    let body = "F(a) == LET G == a' IN G\nI == INSTANCE Nested WITH c <- 1, Op <- F, v <- x";
    let found = check_substitution(body).unwrap_err();
    assert_eq!(found.message, at_most("Nested", "Op", 0));
    // The second error SANY reports for it, alone.
    let nested = "---- MODULE Inner ----\nCONSTANT Op(_)\nVARIABLE v\nUse == Op(v') = 1\n====";
    let source = "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nF(a) == a + 1\nG(a) == LET H == a' IN 1\nI == INSTANCE Inner WITH Op <- F, v <- x\nJ == INSTANCE Inner WITH Op <- G, v <- x\n====";
    let found = error(source, &[("Inner", nested)]);
    assert_eq!(
        found.message,
        "Level error in instantiating module 'Inner':\nThe level of the argument 1 of the operator G \nmust be at least 2."
    );
}

#[test]
fn accepts_substitutions_within_the_levels_a_module_allows() {
    for body in [
        "I == INSTANCE Stateful WITH c <- 1, Op <- LAMBDA a : a + 1, v <- x",
        "I == INSTANCE Pure WITH c <- x, Op <- LAMBDA a : a + x",
        "I == INSTANCE Pure WITH c <- x', Op <- LAMBDA a : a",
        "I == INSTANCE Vars WITH v <- ENABLED (x' = 1), w <- x",
        "I == INSTANCE Applied WITH c <- x', Op <- LAMBDA a : a + 1",
        "I == INSTANCE Applied WITH c <- [](x = 1), Op <- LAMBDA a : a",
        "I == INSTANCE Assumed WITH C <- x', D <- x'",
        "I == INSTANCE Outer WITH c <- x'",
        "I == INSTANCE Nested WITH c <- 1, Op <- LAMBDA a : a = 1, v <- x",
        "I == INSTANCE Twice WITH c <- [](x = 1), Op <- LAMBDA a, b : a",
        "P(k) == INSTANCE Stateful WITH c <- k, Op <- LAMBDA a : a + k, v <- x",
        "Foo == LET k == 1\n           I == INSTANCE Stateful WITH c <- k, Op <- LAMBDA a : a, v <- x IN I!Use",
        "Foo == \\E k \\in {1} : LET I == INSTANCE Stateful WITH c <- k, Op <- LAMBDA a : a, v <- x IN I!Use",
        "F(a) == x' + a\nI == INSTANCE Pure WITH c <- 1, Op <- F",
        "F(a) == LET G == a' IN G\nI == INSTANCE Pure WITH c <- 1, Op <- F",
        "F(a) == LET G == 1 IN a' + G\nI == INSTANCE Pure WITH c <- 1, Op <- F",
        "F(a) == LET G(b) == b' IN G(a)\nI == INSTANCE Pure WITH c <- 1, Op <- F",
        "H(K(_)) == K(1)\nF(a) == H(LAMBDA b : a') + 1\nI == INSTANCE Pure WITH c <- 1, Op <- F",
        "P(G(_)) == INSTANCE Pure WITH c <- 1, Op <- G\nF(a) == a'\nUse == P(F)!Use",
    ] {
        check_substitution(body).unwrap_or_else(|error| panic!("{body}: {error}"));
    }
}

#[test]
fn checks_a_nested_module_without_the_names_around_it() {
    // The variable of the enclosing module doesn't make the nested module non-constant.
    let source = "---- MODULE M ----\nVARIABLE x\n---- MODULE Inner ----\nCONSTANT c\nASSUME c = {}\n====\nI == INSTANCE Inner WITH c <- [](x = 0)\n====";
    let found = error(source, &[]);
    assert_eq!(found.message, at_most("Inner", "c", 2));
    assert_eq!((found.line, found.column), (7, 1));
}
