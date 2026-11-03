use std::collections::HashMap;

use tla_resolve::{DefBody, Spec};

use super::{Plan, Usage, plan};
use crate::liveness::template::Template;
use crate::testing::spec;

fn planned(body: &str, config: &str) -> Result<(Spec, Plan), String> {
    let mut spec = spec(body);
    let config = tla_parser::parse_config(config).unwrap();
    plan(&mut spec, &config, &HashMap::new())
        .map(|plan| (spec, plan))
        .map_err(|error| error.message)
}

fn name(spec: &Spec, def: tla_resolve::DefId) -> &str {
    spec.def(def).name.as_str()
}

const SPEC: &str = "vars == <<x>>\nInit == x = 0\nNext == x' = x + 1\nLive == WF_vars(Next)\nSpec == Init /\\ [][Next]_vars /\\ Live";

#[test]
fn splits_a_specification_into_init_next_and_fairness() {
    let (spec, plan) = planned(SPEC, "SPECIFICATION Spec").unwrap();
    let init: Vec<&str> = plan.init.iter().map(|&def| name(&spec, def)).collect();
    assert_eq!((init, plan.next.map(|def| name(&spec, def))), (vec!["Init"], Some("Next")));
    // TLC translates the fairness only to check temporal properties.
    assert!(plan.fairness.is_empty());
    let body = format!("{SPEC}\nLater == <>(x > 2)");
    let (_, plan) = planned(&body, "SPECIFICATION Spec\nPROPERTY Later").unwrap();
    assert!(matches!(plan.fairness[..], [Template::Fairness { strong: false, .. }]));
    assert!(matches!(&plan.properties[..], [(name, Template::Eventually(body))]
        if name == "Later" && matches!(**body, Template::State(_))));

    // Parts that aren't definitions get definitions of their own.
    let (spec, plan) = planned(
        "Spec == x = 0 /\\ x \\in Nat /\\ [][x' = x + 1 \\/ x' = 0]_x",
        "SPECIFICATION Spec",
    )
    .unwrap();
    assert_eq!(plan.init.len(), 2);
    let next = spec.def(plan.next.unwrap());
    assert!(next.params.is_empty() && matches!(next.body, DefBody::Expr(_)));
    assert_eq!(spec.levels.len(), spec.defs.len());
}

#[test]
fn sorts_the_parts_of_properties() {
    let body = format!(
        "{SPEC}\nTypeOK == x \\in Nat\nInv == []TypeOK\nUp == [][x' > x]_x\nStart == x = 0\nEventually == <>(x = 3)\nAll == Inv /\\ Up /\\ Start /\\ Eventually"
    );
    let (_, plan) = planned(&body, "SPECIFICATION Spec\nPROPERTY All").unwrap();
    let names =
        |checks: &[super::Check]| checks.iter().map(|check| check.name.clone()).collect::<Vec<_>>();
    assert_eq!(names(&plan.invariants), ["TypeOK"]);
    assert_eq!(names(&plan.action_properties), ["Up"]);
    assert_eq!(names(&plan.initial_predicates), ["Start"]);
    let properties: Vec<&str> = plan.properties.iter().map(|(name, _)| name.as_str()).collect();
    assert_eq!(properties, ["Eventually"]);
}

#[test]
fn defers_constant_parts_to_evaluation() {
    let body = format!("{SPEC}\nN == 3\nTrue == TRUE\nBig == N > 2");
    let (_, plan) = planned(&body, "SPECIFICATION Spec\nINVARIANT True\nPROPERTY Big").unwrap();
    let usages: Vec<&Usage> = plan.constants.iter().map(|constant| &constant.usage).collect();
    assert!(matches!(usages[0], Usage::Predicate { kind: "invariant", .. }));
    assert!(matches!(usages[1], Usage::Predicate { kind: "property", .. }));
    // An operator applied to a variable is at state level to TLC, whether it uses its
    // parameter or not.
    let body = format!("{SPEC}\nIgnore(a) == FALSE\nInv == Ignore(x)");
    let (_, plan) = planned(&body, "SPECIFICATION Spec\nINVARIANT Inv").unwrap();
    assert!(plan.constants.is_empty());
    assert_eq!(plan.invariants.len(), 1);
}

#[test]
fn rejects_what_tlc_rejects() {
    let body =
        format!("{SPEC}\nAct == x' = x\nOp(a) == a\nTwice == [][Next]_x /\\ [][Next]_x /\\ Init");
    for (config, message) in [
        (
            "SPECIFICATION Nope",
            "The name Nope specified in the configuration file\nis not defined in the specification.",
        ),
        (
            "INIT Init\nNEXT Next\nSPECIFICATION Spec",
            "The configuration file cannot specify both INIT/NEXT and SPECIFICATION fields.",
        ),
        ("SPECIFICATION Op", "TLC requires Op not to take any argument."),
        (
            "INIT Op\nNEXT Next",
            "TLC requires initial predicate not to take any argument, but one was given: Op",
        ),
        (
            "SPECIFICATION Spec\nINVARIANT Act",
            "The invariant Act is not a state predicate (one with no primes or temporal operators).",
        ),
        ("SPECIFICATION Twice", "The specification Twice must contain at most one [][Next]_vars"),
        ("SPECIFICATION Spec\nPROPERTY Act", "The property Act is an action-level formula"),
        ("NEXT Next", "The configuration file did not specify the initial state predicate."),
        (
            "INIT Init\nINVARIANT Init",
            "The configuration file did not specify the next state predicate.",
        ),
    ] {
        assert_eq!(planned(&body, config).unwrap_err(), message, "{config}");
    }
}

#[test]
fn follows_parameterized_instances() {
    let inner = "---- MODULE Inner ----\nEXTENDS Naturals\nVARIABLE v\n\
        Spec == v = 0 /\\ [][v' = (v + 1) % 3]_v\n====\n";
    let source =
        "---- MODULE M ----\nVARIABLE x\nI(v) == INSTANCE Inner\nSpec == I(x)!Spec\n====\n";
    let mut spec = tla_resolve::resolve(source, &mut |name: &str| {
        (name == "Inner").then(|| inner.to_string())
    })
    .unwrap_or_else(|error| panic!("{error}"));
    let config = tla_parser::parse_config("SPECIFICATION Spec").unwrap();
    let plan = plan(&mut spec, &config, &HashMap::new()).unwrap();
    assert_eq!(plan.init.len(), 1);
    // The parts are module-level definitions that call into the instance.
    let parts: Vec<_> = plan.init.iter().chain(&plan.next).collect();
    assert!(parts.len() == 2 && parts.iter().all(|&&def| spec.def(def).depth == 0));
}

#[test]
fn checks_invariants_by_sanys_levels() {
    // SANY's level of `Gen(Step, 3)` is that of `ENABLED`, whatever the level of `Step`.
    let body =
        format!("{SPEC}\nStep(k) == x' = k\nGen(A(_), k) == ENABLED A(k)\nInv == Gen(Step, 3)");
    let (_, plan) = planned(&body, "SPECIFICATION Spec\nINVARIANT Inv").unwrap();
    assert_eq!(plan.invariants.len(), 1);
    let error = planned(&body, "SPECIFICATION Spec\nINVARIANT Next").unwrap_err();
    assert!(error.starts_with("The invariant Next is not a state predicate"), "{error}");
}
