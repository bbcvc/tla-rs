//! TLC's string order decides what `CHOOSE` picks and how sets print. The order is process-wide,
//! so these tests run in their own process, one at a time.

mod common;

use std::sync::{Arc, Mutex};

use common::{eval, module};
use tla_tools_eval::{Evaluator, bind_model, value::set_order};

static ORDER: Mutex<()> = Mutex::new(());

/// Evaluates `names` of the module `Test` with `body` under TLC's string order for the model
/// configuration `config`.
fn evaluate_in_tlc_order(body: &str, config: &str, names: &[&str]) -> Vec<String> {
    let source = module(body);
    let config = tla_tools_parser::parse_config(config).unwrap();
    let order = tla_tools_resolve::tlc_string_order(&source, &config, &mut |_: &str| None).unwrap();
    set_order(order.iter().map(String::as_str));
    let spec = tla_tools_resolve::resolve(&source, &mut |_: &str| None).unwrap();
    let model = bind_model(&spec, &config).unwrap();
    let evaluator = Evaluator::new(Arc::new(spec), model.constants).with_overrides(model.overrides);
    names.iter().map(|name| eval(&evaluator, name).unwrap().to_string()).collect()
}

#[test]
fn orders_strings_by_when_tlc_interns_them() {
    let _order = ORDER.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    // This process interns "alpha" first, but TLC interns the literals' contents in the order
    // the module writes them.
    tla_tools_eval::value::Symbol::intern("alpha");
    let body =
        "Set == {\"zeta\", \"alpha\"}\nFirst == CHOOSE s \\in Set : TRUE\nR == [b |-> 1, a |-> 2]";
    assert_eq!(
        evaluate_in_tlc_order(body, "", &["Set", "First", "R"]),
        ["{\"zeta\", \"alpha\"}", "\"zeta\"", "[b |-> 1, a |-> 2]"]
    );
}

#[test]
fn orders_model_values_as_the_configuration_writes_them() {
    let _order = ORDER.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    let body = "CONSTANT Procs\nAll == Procs\nFirst == CHOOSE p \\in Procs : TRUE";
    assert_eq!(
        evaluate_in_tlc_order(body, "CONSTANT Procs = {p2, p1}", &["All", "First"]),
        ["{p2, p1}", "p2"]
    );
}

/// TLC's fingerprint of a model value includes its place in TLC's intern order, which seeds the
/// random choices TLC makes in each state.
#[test]
fn fingerprints_model_values_by_their_intern_number() {
    let _order = ORDER.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    let body = "EXTENDS TLCExt\nCONSTANT Procs\nFP1 == TLCFP(CHOOSE p \\in Procs : TRUE)\nFP2 == TLCFP(<<Procs>>)";
    // The values tla-ts's getTlcFingerprint gives under the same order.
    assert_eq!(
        evaluate_in_tlc_order(body, "CONSTANT Procs = {p2, p1}", &["FP1", "FP2"]),
        ["-887695703", "1692085849"]
    );
}
