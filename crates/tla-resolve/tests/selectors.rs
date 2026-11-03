//! Subexpression references: what they resolve to, and the errors SANY reports for them. The
//! error cases come from tla-ts, which checked them against SANY.

use std::collections::HashMap;

use tla_resolve::{DefBody, ExprKind, Level, ResolveError, RootName, Scope, Spec, resolve};

fn resolve_with(root: &str, modules: &[(&str, &str)]) -> Result<Spec, ResolveError> {
    let modules: HashMap<String, String> =
        modules.iter().map(|(name, source)| (name.to_string(), source.to_string())).collect();
    resolve(root, &mut |name: &str| modules.get(name).cloned())
}

fn module(body: &str) -> String {
    format!("---- MODULE M ----\nEXTENDS Naturals\n{body}\n====")
}

fn spec(body: &str) -> Spec {
    resolve_with(&module(body), &[]).unwrap_or_else(|error| panic!("{error}"))
}

fn error(body: &str) -> String {
    resolve_with(&module(body), &[]).expect_err("resolution should fail").message
}

fn body<'s>(spec: &'s Spec, name: &str) -> &'s ExprKind {
    let Some(RootName::Def(id)) = spec.lookup(name) else { panic!("{name} isn't defined") };
    match &spec.def(id).body {
        DefBody::Expr(expr) => &expr.kind,
        DefBody::Function { .. } => panic!("{name} is a function"),
    }
}

#[test]
fn resolves_a_reference_to_a_definition_of_the_selected_part() {
    let spec = spec(
        "Inv == /\\ 1 = 1\n       /\\ 2 > 1\nSecond == Inv!2\nOp(a) == lab :: a + 1\nAt == Op(3)!lab",
    );
    let ExprKind::Call { def, scope: Scope::Global, args } = body(&spec, "Second") else {
        panic!("Inv!2 is a call")
    };
    assert!(args.is_empty());
    let selection = spec.def(*def);
    assert_eq!((selection.name.as_str(), selection.depth), ("Inv!2", 0));
    let DefBody::Expr(expr) = &selection.body else { panic!() };
    assert!(matches!(expr.kind, ExprKind::Call { .. }), "the selected 2 > 1 applies >");

    let ExprKind::Call { def, args, .. } = body(&spec, "At") else { panic!("Op(3)!lab is a call") };
    assert_eq!(spec.def(*def).params, [0]);
    assert_eq!(args[0].kind, ExprKind::Int(3));
}

#[test]
fn selects_through_a_parameterized_instance() {
    let inner = "---- MODULE Inner ----\nEXTENDS Naturals\nCONSTANT c\nOp(a) == sum :: a + c\n====";
    let source = module("P(k) == INSTANCE Inner WITH c <- k\nX == P(1)!Op(2)!sum");
    let spec = resolve_with(&source, &[("Inner", inner)]).unwrap_or_else(|error| panic!("{error}"));
    let ExprKind::Call { def, scope: Scope::Instance { args: instance_args, .. }, args } =
        body(&spec, "X")
    else {
        panic!("P(1)!Op(2)!sum calls the selection in the instance's frame")
    };
    assert_eq!((instance_args.len(), args.len()), (1, 1));
    assert_eq!(spec.def(*def).depth, 1);
}

#[test]
fn rejects_references_sany_rejects() {
    let definitions = "Op(a) == lab :: a\nOp2(a, b) == lab2 :: a\nOp3 == \\A y \\in {1} : in(y) :: y = 1\nTHEOREM thm == lt :: TRUE\nIf == IF TRUE THEN 1 ELSE 2\nLet == LET L == 1 IN L";
    for (reference, message) in [
        ("Op!lab(1)", "The operator Op requires 1 arguments."),
        ("Op2(1)!lab2", "The operator Op2 requires 2 arguments."),
        ("Op(1)!nolab", "Cannot find label `nolab'."),
        ("thm!nolab", "Cannot find label `nolab'."),
        ("Op(1)!lab(2)", "Label `lab' used with wrong number of arguments."),
        ("Op3!in", "Label `in' used with wrong number of arguments."),
        ("If!4", "Nonexistent operand specified by `argument selector 4'."),
        ("Let!2", "A LET/IN expression has only one operand"),
        ("If!1!Name", "A name selector here must be from a LET clause."),
        ("Let!1!Other", "A name selector here must be from a LET clause."),
        ("Nowhere!1", "Unknown operator: `Nowhere'."),
        ("Op3!@", "The subexpression requires 1 arguments but received 0."),
    ] {
        let found = error(&format!("{definitions}\nX == {reference}"));
        assert_eq!(found, message, "{reference}");
    }
}

#[test]
fn rejects_an_operator_argument_of_the_wrong_arity() {
    let found = error("F(G(_, _)) == G(1, 2)\nOp(a) == a + 1\nX == F(Op!:)");
    assert_eq!(found, "Expected an operator of 2 arguments here.");
}

#[test]
fn levels_a_selection_and_hides_an_action_under_a_label() {
    let spec = spec(
        "VARIABLE x\nNext == /\\ x' = x + 1\n        /\\ x < 3\nGuard == Next!2\nStep == Next!1\nL == [](lab :: x')",
    );
    let level = |name: &str| {
        let Some(RootName::Def(id)) = spec.lookup(name) else { panic!() };
        spec.level(id)
    };
    assert_eq!(
        [level("Guard"), level("Step"), level("L")],
        [Level::State, Level::Action, Level::Temporal]
    );
}
