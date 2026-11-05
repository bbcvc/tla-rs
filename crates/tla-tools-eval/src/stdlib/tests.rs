//! Checks that every definition TLC overrides in a standard module gets a native, so no
//! placeholder definition is ever evaluated in its place.

use std::sync::Arc;

use crate::Evaluator;

/// The top-level definitions of standard modules that TLC evaluates from their TLA+ source.
const EVALUATED_FROM_SOURCE: &[(&str, &str)] = &[
    ("Bags", "Sum"),
    ("Json", "IsSequence"),
    ("Json", "ToJsonKeyValue"),
    ("Json", "ToJsonObjectString"),
    ("Json", "ToJsonArrayString"),
    ("Json", "ToJsonString"),
    ("_Possible", "_Update"),
    ("_Possible", "_Merge"),
];

fn evaluator_for(modules: &str) -> Evaluator {
    let source = format!("---- MODULE T ----\nEXTENDS {modules}\n====\n");
    let spec =
        tla_tools_resolve::resolve(&source, &mut |_: &str| None).expect("the modules resolve");
    Evaluator::new(Arc::new(spec), Vec::new())
}

#[test]
fn overrides_every_definition_tlc_overrides() {
    let evaluator = evaluator_for(
        "Naturals, Integers, Sequences, FiniteSets, TLC, TLCExt, Bags, Json, Randomization, Reals, Toolbox, _Possible",
    );
    let spec = evaluator.spec();
    let mut missing = Vec::new();
    let mut modules = std::collections::BTreeSet::new();
    for (index, def) in spec.defs.iter().enumerate() {
        let module = spec.modules[def.module.index()].name.as_str();
        if def.depth > 0 || !tla_tools_resolve::is_standard_module(module) {
            continue;
        }
        modules.insert(module);
        let is_from_source = matches!(module, "Reals" | "RealTime" | "Toolbox")
            || EVALUATED_FROM_SOURCE.contains(&(module, def.name.as_str()));
        if evaluator.natives[index].is_some() == is_from_source {
            missing.push(format!("{module}!{}", def.name));
        }
    }
    assert!(missing.is_empty(), "wrongly overridden or not: {missing:?}");
    let expected = [
        "Bags",
        "FiniteSets",
        "Integers",
        "Json",
        "Naturals",
        "Randomization",
        "Reals",
        "Sequences",
        "TLC",
        "TLCExt",
        "Toolbox",
        "_Possible",
    ];
    assert!(expected.iter().all(|module| modules.contains(module)), "{modules:?}");
}

#[test]
fn uses_the_arithmetic_of_integers_once_a_spec_loads_it() {
    let naturals = evaluator_for("Naturals");
    let with_integers = evaluator_for("Naturals, TLCExt");
    let divide = |evaluator: &Evaluator| {
        let spec = evaluator.spec();
        let index = spec
            .defs
            .iter()
            .position(|def| {
                def.name.as_str() == "\\div"
                    && spec.modules[def.module.index()].name.as_str() == "Naturals"
            })
            .expect("Naturals defines \\div");
        let native = evaluator.natives[index].expect("\\div has a native");
        let args = [
            crate::Arg::Value(tla_tools_value::Value::Int(-1)),
            crate::Arg::Value(tla_tools_value::Value::Int(2)),
        ];
        native(&mut crate::Ctx::new(evaluator, None), &args).unwrap().as_int()
    };
    assert_eq!(divide(&naturals), Some(0));
    assert_eq!(divide(&with_integers), Some(-1));
}
