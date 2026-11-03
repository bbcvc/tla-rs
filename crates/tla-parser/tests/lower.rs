use tla_ast::{
    Bound, ExceptKey, Expr, ExprKind, Fairness, Module, Op, OpDecl, Pattern, Quantifier, Symbol,
    Unit,
};
use tla_parser::parse_module;

fn parse(source: &str) -> Module {
    parse_module(source).unwrap_or_else(|error| panic!("{error}"))
}

fn definition<'m>(module: &'m Module, name: &str) -> &'m tla_ast::OperatorDef {
    module
        .units
        .iter()
        .find_map(|unit| match unit {
            Unit::Operator(definition) if definition.name.symbol.as_str() == name => {
                Some(definition)
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("no definition named {name}"))
}

fn body<'m>(module: &'m Module, name: &str) -> &'m ExprKind {
    &definition(module, name).body.kind
}

fn apply_name(expr: &Expr) -> &'static str {
    match &expr.kind {
        ExprKind::Apply { name, .. } => name.symbol.as_str(),
        other => panic!("expected an application, found {other:?}"),
    }
}

fn names(pattern: &Pattern) -> Vec<&'static str> {
    match pattern {
        Pattern::Names(names) | Pattern::Tuple(names) => {
            names.iter().map(|name| name.symbol.as_str()).collect()
        }
    }
}

const COMMIT: &str = r#"
Text before the module is ignored.
------------------------------ MODULE Commit ------------------------------
EXTENDS Naturals, FiniteSets
CONSTANT Participants
VARIABLES participantState, prepared

vars == <<participantState, prepared>>

Init == /\ participantState = [participant \in Participants |-> "working"]
        /\ prepared = {}

Prepare(participant) ==
  /\ participantState[participant] = "working"
  /\ participantState' = [participantState EXCEPT ![participant] = "prepared"]
  /\ UNCHANGED <<prepared>>

Next == \E participant \in Participants : Prepare(participant)

Spec == Init /\ [][Next]_vars
=============================================================================
"#;

#[test]
fn lowers_a_specification() {
    let module = parse(COMMIT);
    assert_eq!(module.name.symbol.as_str(), "Commit");
    let extends: Vec<_> = module.extends.iter().map(|name| name.symbol.as_str()).collect();
    assert_eq!(extends, ["Naturals", "FiniteSets"]);
    assert!(matches!(&module.units[0], Unit::Constants(constants) if constants.len() == 1));
    assert!(matches!(&module.units[1], Unit::Variables(variables) if variables.len() == 2));

    let ExprKind::And(conjuncts) = body(&module, "Prepare") else { panic!() };
    assert_eq!(conjuncts.len(), 3);
    let ExprKind::Infix { op: Op::Eq, lhs, rhs } = &conjuncts[1].kind else { panic!() };
    assert!(matches!(&lhs.kind, ExprKind::Postfix { op: Op::Prime, .. }));
    let ExprKind::Except { updates, .. } = &rhs.kind else { panic!() };
    assert!(matches!(&updates[0].path[..], [ExceptKey::Apply(args)] if args.len() == 1));
    assert!(matches!(
        &conjuncts[2].kind,
        ExprKind::Prefix { op: Op::Unchanged, arg } if matches!(arg.kind, ExprKind::Tuple(_))
    ));

    let ExprKind::Quant { quantifier: Quantifier::Exists, bounds, body: action } =
        body(&module, "Next")
    else {
        panic!()
    };
    assert_eq!(names(&bounds[0].pattern), ["participant"]);
    assert!(matches!(&action.kind, ExprKind::Apply { args, .. } if args.len() == 1));

    let ExprKind::And(parts) = body(&module, "Spec") else { panic!() };
    let ExprKind::Prefix { op: Op::Always, arg } = &parts[1].kind else { panic!() };
    let ExprKind::BoxAction { action, sub } = &arg.kind else { panic!() };
    assert_eq!((apply_name(action), apply_name(sub)), ("Next", "vars"));
}

const SHAPES: &str = r#"
---- MODULE Shapes ----
EXTENDS Naturals
CONSTANTS N, Op(_), _ ** _
VARIABLE x
a ++ b == a + b
-. a == 0 - a
RECURSIVE Fact(_)
Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)
f[i \in 1..3, j \in {1}] == i + j
M == INSTANCE Other WITH y <- x, \oplus <- ++
P(z) == INSTANCE Other
LOCAL L == 1
Except == [x EXCEPT ![1] = @ + 1, !.a.b[2, 3] = 4]
Case == CASE x = 1 -> 2 [] x = 2 -> 3 [] OTHER -> 4
Let == LET u == 1 v(w) == w IN u + v(2)
Choose == CHOOSE <<p, q>> \in S : p > q
Sets == {y \in S : y > 1} \cup {y + 1 : y \in S, <<p, q>> \in T}
Product == S \X T \X U
Nested == (S \X T) \X U
Refs == M!Foo(1) + P(2)!Bar + r.field + f[1, 2] + -x + Op(LAMBDA k : k, +)
Literals == <<\b101, \h1F, \o17, "a\"b\n", TRUE, Nat, STRING>>
Fair == WF_x(A) /\ SF_<<x>>(B) /\ \EE z : z /\ <<A>>_x
Records == [a |-> 1, b |-> 2] \in [a : S, b : T]
ASSUME N > 0
THEOREM Thm == TRUE
====
"#;

#[test]
fn lowers_symbolic_and_parameterized_definitions() {
    let module = parse(SHAPES);
    let Unit::Constants(constants) = &module.units[0] else { panic!() };
    let arities: Vec<_> =
        constants.iter().map(|OpDecl { name, arity }| (name.symbol.as_str(), *arity)).collect();
    assert_eq!(arities, [("N", 0), ("Op", 1), ("**", 2)]);

    let plus_plus = definition(&module, "++");
    assert_eq!(plus_plus.params.len(), 2);
    assert_eq!(definition(&module, "-.").params.len(), 1);
    assert!(module.units.iter().any(|unit| matches!(unit,
        Unit::Recursive(declarations) if declarations[0].arity == 1)));

    let function = module.units.iter().find_map(|unit| match unit {
        Unit::Function(function) => Some(function),
        _ => None,
    });
    assert_eq!(function.unwrap().bounds.len(), 2);

    let instances: Vec<_> = module
        .units
        .iter()
        .filter_map(|unit| match unit {
            Unit::ModuleDef(definition) => Some(definition),
            _ => None,
        })
        .collect();
    let substitutions: Vec<_> = instances[0]
        .instance
        .substitutions
        .iter()
        .map(|substitution| (substitution.name.symbol.as_str(), apply_name(&substitution.value)))
        .collect();
    assert_eq!(substitutions, [("y", "x"), ("\\oplus", "++")]);
    assert_eq!(instances[1].params.len(), 1);

    assert!(module.units.iter().any(|unit| matches!(unit,
        Unit::Operator(definition) if definition.is_local && definition.name.symbol.as_str() == "L")));
    assert!(module.units.iter().any(|unit| matches!(unit, Unit::Assume(_))));
    assert!(module.units.iter().any(|unit| matches!(unit,
        Unit::Theorem(theorem) if theorem.name.is_some())));
}

#[test]
fn lowers_compound_expressions() {
    let module = parse(SHAPES);

    let ExprKind::Except { updates, .. } = body(&module, "Except") else { panic!() };
    assert!(
        matches!(&updates[0].value.kind, ExprKind::Infix { lhs, .. } if lhs.kind == ExprKind::At)
    );
    let path = &updates[1].path;
    assert!(matches!(&path[..], [ExceptKey::Field(a), ExceptKey::Field(b), ExceptKey::Apply(args)]
        if a.symbol.as_str() == "a" && b.symbol.as_str() == "b" && args.len() == 2));

    let ExprKind::Case { arms, other } = body(&module, "Case") else { panic!() };
    assert_eq!(arms.len(), 2);
    assert_eq!(other.as_ref().unwrap().kind, ExprKind::Int(4));

    let ExprKind::Let { defs, .. } = body(&module, "Let") else { panic!() };
    assert_eq!(defs.len(), 2);

    let ExprKind::Choose { pattern, set, .. } = body(&module, "Choose") else { panic!() };
    assert!(matches!(pattern, Pattern::Tuple(_)));
    assert_eq!(names(pattern), ["p", "q"]);
    assert!(set.is_some());

    let ExprKind::Infix { op: Op::Cup, lhs, rhs } = body(&module, "Sets") else { panic!() };
    assert!(matches!(&lhs.kind, ExprKind::SetFilter { .. }));
    let ExprKind::SetMap { bounds, .. } = &rhs.kind else { panic!() };
    assert!(matches!(&bounds[1], Bound { pattern: Pattern::Tuple(names), .. } if names.len() == 2));

    assert!(matches!(body(&module, "Product"), ExprKind::Product(factors) if factors.len() == 3));
    let ExprKind::Product(factors) = body(&module, "Nested") else { panic!() };
    assert_eq!(factors.len(), 2);
    assert!(matches!(&factors[0].kind, ExprKind::Product(inner) if inner.len() == 2));
}

#[test]
fn lowers_references_and_literals() {
    let module = parse(SHAPES);

    let mut terms = Vec::new();
    let mut current = body(&module, "Refs");
    while let ExprKind::Infix { op: Op::Plus, lhs, rhs } = current {
        terms.push(&rhs.kind);
        current = &lhs.kind;
    }
    terms.push(current);
    terms.reverse();
    let ExprKind::Qualified { path, name, args } = terms[0] else { panic!() };
    assert_eq!((path[0].name.symbol.as_str(), name.symbol.as_str(), args.len()), ("M", "Foo", 1));
    let ExprKind::Qualified { path, name, .. } = terms[1] else { panic!() };
    assert_eq!((path[0].args.len(), name.symbol.as_str()), (1, "Bar"));
    assert!(matches!(terms[2], ExprKind::Dot { field, .. } if field.symbol.as_str() == "field"));
    assert!(matches!(terms[3], ExprKind::FuncApp { args, .. } if args.len() == 2));
    assert!(matches!(terms[4], ExprKind::Prefix { op: Op::Negate, .. }));
    let ExprKind::Apply { args, .. } = terms[5] else { panic!() };
    assert!(matches!(&args[0].kind, ExprKind::Lambda { params, .. } if params.len() == 1));
    assert_eq!(apply_name(&args[1]), "+");

    let ExprKind::Tuple(literals) = body(&module, "Literals") else { panic!() };
    let kinds: Vec<_> = literals.iter().map(|literal| literal.kind.clone()).collect();
    assert_eq!(kinds[..3], [ExprKind::Int(5), ExprKind::Int(31), ExprKind::Int(15)]);
    assert_eq!(kinds[3], ExprKind::Str(Symbol::intern("a\"b\n")));
    assert_eq!(kinds[4], ExprKind::Bool(true));
    assert_eq!((apply_name(&literals[5]), apply_name(&literals[6])), ("Nat", "STRING"));

    let ExprKind::And(parts) = body(&module, "Fair") else { panic!() };
    assert!(matches!(&parts[0].kind, ExprKind::Fairness { fairness: Fairness::Weak, .. }));
    assert!(matches!(&parts[1].kind, ExprKind::Fairness { fairness: Fairness::Strong, .. }));
    let ExprKind::UnboundedQuant { quantifier: Quantifier::TemporalExists, body: inner, .. } =
        &parts[2].kind
    else {
        panic!()
    };
    assert!(matches!(&inner.kind,
        ExprKind::And(inner) if matches!(inner[1].kind, ExprKind::AngleAction { .. })));

    let ExprKind::Infix { op: Op::In, lhs, rhs } = body(&module, "Records") else { panic!() };
    assert!(matches!(&lhs.kind, ExprKind::Record(fields) if fields.len() == 2));
    assert!(matches!(&rhs.kind, ExprKind::RecordSet(fields) if fields.len() == 2));
}

#[test]
fn reports_syntax_errors_with_positions() {
    let source = "---- MODULE Broken ----\nVARIABLE x\nNext == x \\in\nInv == x > 0\n====\n";
    let error = parse_module(source).unwrap_err();
    assert_eq!(error.to_string(), "line 4, column 6: syntax error");

    let error = parse_module("---- MODULE Broken ----\nInit == x = \n====\n").unwrap_err();
    assert_eq!(error.message, "syntax error");

    let error = parse_module("---- MODULE Real ----\nX == 1.5\n====\n").unwrap_err();
    assert_eq!(error.message, "a real number is not supported");
    assert_eq!((error.line, error.column), (2, 6));

    assert_eq!(parse_module("no module here").unwrap_err().message, "no module found");
}

#[test]
fn aligns_tabs_to_eight_columns_like_sany() {
    let source =
        "---- MODULE Tabs ----\nVARIABLE x\nNext == /\\ x' = 1\n\t/\\ x = 0\nS == \"a\tb\"\n====\n";
    let module = parse(source);
    assert!(matches!(body(&module, "Next"), ExprKind::And(conjuncts) if conjuncts.len() == 2));
    assert_eq!(body(&module, "S"), &ExprKind::Str(Symbol::intern("a\tb")));
    let span = definition(&module, "S").body.span;
    assert_eq!(&source[span.start as usize..span.end as usize], "\"a\tb\"");
}

#[test]
fn ignores_plus_cal_it_cannot_read_inside_comments() {
    let source = "---- MODULE Comment ----\n(* --algorithm A { fair { while (TRUE) { skip } } } *)\nX == 1\n====\n";
    assert!(matches!(body(&parse(source), "X"), ExprKind::Int(1)));
}

#[test]
fn parses_every_module_in_a_file() {
    let source = "---- MODULE A ----\nX == 1\n====\n---- MODULE B ----\nTHEOREM T == TRUE\n====\n";
    let modules = tla_parser::parse_modules(source).unwrap();
    let names: Vec<_> = modules.iter().map(|module| module.name.symbol.as_str()).collect();
    assert_eq!(names, ["A", "B"]);
    assert!(matches!(&modules[1].units[0],
        Unit::Theorem(theorem) if theorem.statement.as_ref().unwrap().kind == ExprKind::Bool(true)));
}
