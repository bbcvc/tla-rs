use std::sync::Arc;

use tla_tools_resolve::RootName;
use tla_tools_value::Value;

use crate::Evaluator;
use crate::stdlib::tlc::JavaRandom;

fn evaluator(body: &str) -> Evaluator {
    let source = format!("---- MODULE T ----\n{body}\n====\n");
    let spec = tla_tools_resolve::resolve(&source, &mut |_: &str| None).unwrap();
    Evaluator::new(Arc::new(spec), Vec::new())
}

fn def(evaluator: &Evaluator, name: &str) -> tla_tools_resolve::DefId {
    match evaluator.spec().lookup(name) {
        Some(RootName::Def(def)) => def,
        other => panic!("{name} is {other:?}"),
    }
}

fn is_constant(evaluator: &Evaluator, name: &str) -> bool {
    evaluator.is_computed_once(def(evaluator, name))
}

#[test]
fn computes_once_the_definitions_tla_ts_finds_constant() {
    let evaluator = evaluator(
        "EXTENDS Naturals, TLC\nVARIABLE x\n\
         Sum == 1 + 1\nState == x\nGet == TLCGet(1)\nThroughGet == Get + 1\n\
         Op(p) == p\nLet == LET G == 1 IN G\nf[n \\in 1..3] == n\nRandom == RandomElement(1..10)\n\
         Printed == Print(1, 2)",
    );
    for name in ["Sum", "Let", "f", "Random", "Printed"] {
        assert!(is_constant(&evaluator, name), "{name} is constant");
    }
    for name in ["State", "Get", "ThroughGet", "Op"] {
        assert!(!is_constant(&evaluator, name), "{name} is not constant");
    }
    // A native replaces TLC's own definitions.
    let java_time = evaluator.spec().defs.iter().position(|def| def.name.as_str() == "JavaTime");
    assert!(!evaluator.is_computed_once(tla_tools_resolve::DefId(java_time.unwrap() as u32)));
}

#[test]
fn computes_a_constant_definition_once() {
    let evaluator = evaluator("EXTENDS Naturals, TLC\nP == Print(\"once\", 1)\nQ == P + P");
    let q = evaluator.eval_def(def(&evaluator, "Q"), None).unwrap();
    assert_eq!(q.as_int(), Some(2));
    evaluator.eval_def(def(&evaluator, "Q"), None).unwrap();
    assert_eq!(*evaluator.runtime().output.lock().unwrap(), ["\"once\"  1"]);
}

#[test]
fn draws_from_the_startup_generator_once() {
    let evaluator =
        evaluator("EXTENDS Naturals, TLC\nR == RandomElement(1..1000)\nPair == <<R, R>>");
    evaluator.runtime().set_seed(4);
    let pair = evaluator.eval_def(def(&evaluator, "Pair"), None).unwrap();
    let expected = 1 + (JavaRandom::new(4).next_double() * 1000.0).floor() as i32;
    assert_eq!(pair.to_string(), format!("<<{expected}, {expected}>>"));
}

#[test]
fn enumerates_a_constant_function_over_an_enumerated_domain() {
    let evaluator = evaluator("EXTENDS Naturals\nf[n \\in 1..3] == n * 2\ng[n \\in Nat] == n");
    let f = evaluator.eval_def(def(&evaluator, "f"), None).unwrap();
    assert!(matches!(f, Value::Tuple(_)), "{f}");
    let g = evaluator.eval_def(def(&evaluator, "g"), None).unwrap();
    assert!(matches!(g, Value::LazyFunc(_)));
}

#[test]
fn computes_the_constant_definitions_at_startup_ignoring_failures() {
    let evaluator = evaluator(
        "EXTENDS Naturals, TLC\nFirst == Print(\"first\", 1)\nBad == 1 \\div 0\nSecond == PrintT(\"second\")",
    );
    evaluator.evaluate_constant_definitions();
    assert_eq!(*evaluator.runtime().output.lock().unwrap(), ["\"first\"  1", "\"second\""]);
    assert!(evaluator.eval_def(def(&evaluator, "Bad"), None).is_err());
    evaluator.eval_def(def(&evaluator, "First"), None).unwrap();
    assert_eq!(evaluator.runtime().output.lock().unwrap().len(), 2);
}
