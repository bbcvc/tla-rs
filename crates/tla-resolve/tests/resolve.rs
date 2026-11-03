use std::collections::HashMap;

use tla_resolve::{
    Builtin, Def, DefBody, Expr, ExprKind, Local, OpRef, Pattern, RootName, Scope, Spec, resolve,
};

fn resolve_with(root: &str, modules: &[(&str, &str)]) -> Result<Spec, tla_resolve::ResolveError> {
    let modules: HashMap<String, String> =
        modules.iter().map(|(name, source)| (name.to_string(), source.to_string())).collect();
    resolve(root, &mut |name: &str| modules.get(name).cloned())
}

fn spec(root: &str, modules: &[(&str, &str)]) -> Spec {
    resolve_with(root, modules).unwrap_or_else(|error| panic!("{error}"))
}

fn error(root: &str, modules: &[(&str, &str)]) -> String {
    resolve_with(root, modules).expect_err("resolution should fail").message
}

fn def<'s>(spec: &'s Spec, name: &str) -> &'s Def {
    match spec.lookup(name) {
        Some(RootName::Def(id)) => spec.def(id),
        other => panic!("{name} is {other:?}"),
    }
}

fn body_of<'s>(spec: &'s Spec, name: &str) -> &'s ExprKind {
    match &def(spec, name).body {
        DefBody::Expr(expr) => &expr.kind,
        DefBody::Function { .. } => panic!("{name} is a function"),
    }
}

fn call_name(spec: &Spec, expr: &Expr) -> String {
    match &expr.kind {
        ExprKind::Call { def, .. } => spec.def(*def).name.to_string(),
        other => panic!("expected a call, found {other:?}"),
    }
}

const COMMIT: &str = r#"
---- MODULE Commit ----
EXTENDS Naturals
CONSTANT Participants
VARIABLES state, count
Init == state = [p \in Participants |-> "working"] /\ count = 0
Prepare(p) == /\ state[p] = "working"
              /\ state' = [state EXCEPT ![p] = "prepared", ![p] = @]
              /\ count' = count + 1
Next == \E p \in Participants : Prepare(p)
====
"#;

#[test]
fn resolves_variables_constants_and_definitions() {
    let spec = spec(COMMIT, &[]);
    assert_eq!(
        spec.variables.iter().map(|var| var.name.as_str()).collect::<Vec<_>>(),
        ["state", "count"]
    );
    assert_eq!(spec.constants.len(), 1);
    assert!(matches!(spec.lookup("count"), Some(RootName::Var(id)) if id.index() == 1));

    let ExprKind::And(conjuncts) = body_of(&spec, "Init") else { panic!() };
    let ExprKind::Builtin { op: Builtin::Eq, args } = &conjuncts[0].kind else { panic!() };
    assert!(matches!(args[0].kind, ExprKind::Var(id) if id.index() == 0));
    let ExprKind::Function { bounds, body } = &args[1].kind else { panic!() };
    assert_eq!(bounds[0].pattern, Pattern::Names(vec![0]));
    assert!(matches!(bounds[0].set.kind, ExprKind::Const(_)));
    assert!(matches!(body.kind, ExprKind::Str(_)));

    let ExprKind::Quant { bounds, body, .. } = body_of(&spec, "Next") else { panic!() };
    assert_eq!(bounds[0].pattern, Pattern::Names(vec![0]));
    let ExprKind::Call { scope: Scope::Global, args, .. } = &body.kind else { panic!() };
    assert_eq!(args[0].kind, ExprKind::Local(Local { hops: 0, slot: 0 }));
}

#[test]
fn resolves_except_at_and_standard_operators() {
    let spec = spec(COMMIT, &[]);
    let prepare = def(&spec, "Prepare");
    assert_eq!(prepare.params, [0]);
    let DefBody::Expr(Expr { kind: ExprKind::And(conjuncts), .. }) = &prepare.body else {
        panic!()
    };
    let ExprKind::Builtin { op: Builtin::Eq, args } = &conjuncts[1].kind else { panic!() };
    assert!(matches!(&args[0].kind, ExprKind::Builtin { op: Builtin::Prime, .. }));
    let ExprKind::Except { updates, .. } = &args[1].kind else { panic!() };
    assert_eq!(updates[1].value.kind, ExprKind::Local(Local { hops: 0, slot: updates[1].at }));
    assert_ne!(updates[0].at, updates[1].at);
    assert_eq!(prepare.frame_size, 3);

    let ExprKind::Builtin { args, .. } = &conjuncts[2].kind else { panic!() };
    assert_eq!(call_name(&spec, &args[1]), "+");
    let plus = match &args[1].kind {
        ExprKind::Call { def, .. } => spec.def(*def),
        _ => unreachable!(),
    };
    assert_eq!(spec.modules[plus.module.index()].name.as_str(), "Naturals");
}

#[test]
fn resolves_let_definitions_as_closures() {
    let spec = spec(
        r#"
---- MODULE Let ----
EXTENDS Naturals
Op(x) == LET y == x + 0
             F(z) == \E w \in {z} : w = y
         IN F(1)
====
"#,
        &[],
    );
    let op = def(&spec, "Op");
    let DefBody::Expr(Expr { kind: ExprKind::Call { def: f, scope, .. }, .. }) = &op.body else {
        panic!()
    };
    assert_eq!(*scope, Scope::Up(0));
    let f = spec.def(*f);
    assert_eq!(f.depth, 1);
    let DefBody::Expr(Expr { kind: ExprKind::Quant { bounds, body, .. }, .. }) = &f.body else {
        panic!()
    };
    assert!(matches!(&bounds[0].set.kind,
        ExprKind::SetEnum(items) if items[0].kind == ExprKind::Local(Local { hops: 0, slot: 0 })));
    let ExprKind::Builtin { args, .. } = &body.kind else { panic!() };
    assert_eq!(args[0].kind, ExprKind::Local(Local { hops: 0, slot: 1 }));
    let ExprKind::Call { def: y, scope, .. } = &args[1].kind else { panic!() };
    assert_eq!(*scope, Scope::Up(1));
    let DefBody::Expr(Expr { kind: ExprKind::Call { args, .. }, .. }) = &spec.def(*y).body else {
        panic!()
    };
    assert_eq!(args[0].kind, ExprKind::Local(Local { hops: 1, slot: 0 }));
}

#[test]
fn resolves_recursion_and_operator_arguments() {
    let spec = spec(
        r#"
---- MODULE Higher ----
EXTENDS Naturals
RECURSIVE Fact(_)
Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)
f[n \in Nat] == IF n = 0 THEN 0 ELSE f[n - 1]
Apply(F(_, _), a, b) == F(a, b)
Sum == Apply(+, 1, 2)
Twice == Apply(LAMBDA a, b : a * b, 3, 4)
====
"#,
        &[],
    );
    let ExprKind::If { otherwise, .. } = body_of(&spec, "Fact") else { panic!() };
    let ExprKind::Call { args, .. } = &otherwise.kind else { panic!() };
    assert_eq!(call_name(&spec, &args[1]), "Fact");
    assert!(matches!(def(&spec, "f").body, DefBody::Function { .. }));

    assert_eq!(def(&spec, "Apply").params, [2, 0, 0]);
    let ExprKind::CallParam { param, .. } = body_of(&spec, "Apply") else { panic!() };
    assert_eq!(*param, Local { hops: 0, slot: 0 });
    let ExprKind::Call { args, .. } = body_of(&spec, "Sum") else { panic!() };
    assert!(matches!(&args[0].kind, ExprKind::OpArg(OpRef::Def { scope: Scope::Global, .. })));
    let ExprKind::Call { args, .. } = body_of(&spec, "Twice") else { panic!() };
    let ExprKind::OpArg(OpRef::Def { def: lambda, scope: Scope::Up(0) }) = &args[0].kind else {
        panic!()
    };
    assert_eq!(spec.def(*lambda).params, [0, 0]);
}

const COUNTER: &str = r#"
---- MODULE Counter ----
EXTENDS Naturals
CONSTANT Max
VARIABLE c
Inc == c < Max /\ c' = c + 1
LOCAL Hidden == 0
====
"#;

#[test]
fn instantiates_modules_with_substitutions() {
    let spec = spec(
        r#"
---- MODULE Root ----
EXTENDS Naturals
VARIABLE x
C == INSTANCE Counter WITH c <- x, Max <- 3
P(m) == INSTANCE Counter WITH c <- x, Max <- m
INSTANCE Counter WITH c <- x, Max <- 5
Next == C!Inc \/ P(7)!Inc \/ Inc
====
"#,
        &[("Counter", COUNTER)],
    );
    assert_eq!(spec.variables.len(), 1, "the instance's variable is substituted, not declared");
    assert!(spec.constants.is_empty());
    assert!(spec.lookup("Hidden").is_none());

    let ExprKind::Or(disjuncts) = body_of(&spec, "Next") else { panic!() };
    let ExprKind::Call { def: named, scope: Scope::Global, .. } = &disjuncts[0].kind else {
        panic!()
    };
    let DefBody::Expr(Expr { kind: ExprKind::And(inc), .. }) = &spec.def(*named).body else {
        panic!()
    };
    let ExprKind::Call { args, .. } = &inc[0].kind else { panic!() };
    assert!(matches!(args[0].kind, ExprKind::Var(_)));
    assert_eq!(args[1].kind, ExprKind::Int(3));

    let ExprKind::Call { def: parameterized, scope, .. } = &disjuncts[1].kind else { panic!() };
    let Scope::Instance { parent, args } = scope else { panic!() };
    assert_eq!(**parent, Scope::Global);
    assert_eq!(args[0].kind, ExprKind::Int(7));
    let inc = spec.def(*parameterized);
    assert_eq!(inc.depth, 1);
    let DefBody::Expr(Expr { kind: ExprKind::And(conjuncts), .. }) = &inc.body else { panic!() };
    let ExprKind::Call { args, .. } = &conjuncts[0].kind else { panic!() };
    let ExprKind::Call { def: max, scope: Scope::Up(1), .. } = &args[1].kind else { panic!() };
    let DefBody::Expr(max_body) = &spec.def(*max).body else { panic!() };
    assert_eq!(max_body.kind, ExprKind::Local(Local { hops: 1, slot: 0 }));

    let ExprKind::Call { def: imported, .. } = &disjuncts[2].kind else { panic!() };
    assert_ne!(imported, named);
}

#[test]
fn follows_sany_visibility_rules() {
    assert_eq!(
        error("---- MODULE A ----\nEXTENDS Sequences\nX == 1 + 2\n====\n", &[]),
        "Unknown operator: `+'."
    );
    assert!(
        error("---- MODULE A ----\nX == Y\nY == 1\n====\n", &[]).starts_with("Unknown operator")
    );
    assert!(
        error("---- MODULE A ----\nVARIABLE x\nX == \\E x \\in {} : TRUE\n====\n", &[])
            .starts_with("Multiply-defined symbol 'x'")
    );
    assert!(
        error("---- MODULE A ----\nF(a) == a\nX == F(1, 2)\n====\n", &[])
            .starts_with("The operator F requires 1 arguments")
    );
    assert!(error("---- MODULE A ----\nEXTENDS Missing\n====\n", &[]).contains("module Missing"));
    assert!(
        error(
            "---- MODULE A ----\nInc == 0\nC == INSTANCE Counter\n====\n",
            &[("Counter", COUNTER)]
        )
        .contains("no substitution for Max")
    );
    assert!(error("---- MODULE A ----\nx \\in y == 1\n====\n", &[]).contains("built-in operator"));
    assert!(
        error("---- MODULE A ----\nRECURSIVE F(_)\nX == 1\n====\n", &[]).contains("never defined")
    );

    let diamond = spec("---- MODULE A ----\nEXTENDS Naturals, Integers\nX == 1 + 2\n====\n", &[]);
    assert_eq!(
        call_name(&diamond, &Expr::new(body_of(&diamond, "X").clone(), Default::default())),
        "+"
    );
}

#[test]
fn rejects_what_sany_rejects_in_definitions() {
    let redefined = "---- MODULE A ----\nG == 1\nX == LET G == 0 IN G\n====\n";
    assert_eq!(error(redefined, &[]), "Operator G already defined or declared.");
    let imported = "---- MODULE A ----\nEXTENDS Naturals\nNat == 1\n====\n";
    assert_eq!(error(imported, &[]), "Operator Nat already defined or declared.");
    let fields = "---- MODULE A ----\nX == [a |-> 1, a |-> 2]\n====\n";
    assert_eq!(error(fields, &[]), "Non-unique fields in constructor.");
    let higher = "---- MODULE A ----\nD(Op(_)) == Op(42)\nX == D(D)\n====\n";
    assert!(error(higher, &[]).starts_with("Expected an operator of 1 arguments"));
}

#[test]
fn resolves_names_sany_defines_implicitly() {
    let spec = spec(
        r#"
---- MODULE Outer ----
EXTENDS Naturals
VARIABLE y
---- MODULE Inner ----
VARIABLE x
Step == x < 3
====
I == INSTANCE Inner WITH x <- y
ASSUME Positive == 1 > 0
AXIOM Granted == 2 > 1
THEOREM Trivial == TRUE
RECURSIVE f
f[n \in Nat] == IF n = 0 THEN 0 ELSE f[n - 1]
O == INSTANCE Other
Check == Positive /\ Trivial /\ I!Step /\ O!Z = 1
====
---- MODULE Other ----
Z == 1
====
"#,
        &[],
    );
    // TLC checks the ASSUME but not the AXIOM, though both define their names.
    assert_eq!(spec.assumptions.len(), 1);
    assert_eq!(def(&spec, "Granted").params.len(), 0);
    assert!(matches!(def(&spec, "f").body, DefBody::Function { .. }));
    let ExprKind::And(conjuncts) = body_of(&spec, "Check") else { panic!() };
    assert_eq!(call_name(&spec, &conjuncts[0]), "Positive");
    assert_eq!(call_name(&spec, &conjuncts[1]), "Trivial");
    let ExprKind::Call { def: step, .. } = &conjuncts[2].kind else { panic!() };
    let DefBody::Expr(Expr { kind: ExprKind::Call { args, .. }, .. }) = &spec.def(*step).body
    else {
        panic!("the nested module sees < from the enclosing module's EXTENDS")
    };
    assert!(matches!(args[0].kind, ExprKind::Var(_)));
}
