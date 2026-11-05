//! Ported from tla-ts `tests/unit/tlc-ext-operators.test.ts` where natives can be called alone.

use std::sync::Arc;

use tla_tools_value::{Result, Symbol, Value};

use crate::stdlib::testing::{call, call_in, error, evaluator, int, operator, string, tuple};
use crate::{Arg, CheckerOptions, Evaluator, Operator};

fn ext(evaluator: &Evaluator, name: &str, args: Vec<Arg>) -> Result<Value> {
    call_in(evaluator, "TLCExt", name, false, args)
}

fn values(args: &[Value]) -> Vec<Arg> {
    args.iter().cloned().map(Arg::Value).collect()
}

#[test]
fn prints_both_values_when_assert_eq_fails() {
    let evaluator = evaluator();
    let equal = ext(&evaluator, "AssertEq", values(&[int(1), int(1)])).unwrap();
    assert_eq!(equal.as_bool(), Some(true));
    let unequal = ext(&evaluator, "AssertEq", values(&[int(1), int(0)])).unwrap();
    assert_eq!(unequal.as_bool(), Some(false));
    let output = evaluator.runtime().output.lock().unwrap().clone();
    assert_eq!(output, ["\"Assertion failed\"", "1", "0"]);
}

#[test]
fn reads_and_updates_registers() {
    let evaluator = evaluator();
    let default = ext(&evaluator, "TLCGetOrDefault", values(&[int(1), string("d")])).unwrap();
    assert_eq!(default.to_string(), "\"d\"");
    let add =
        operator(|args| Ok(Value::Int(args[0].as_int().unwrap() + args[1].as_int().unwrap())));
    let args = vec![Arg::Value(string("s:count")), add, Arg::Value(int(5)), Arg::Value(int(10))];
    let previous = ext(&evaluator, "TLCGetAndSet", args).unwrap();
    assert_eq!(previous.as_int(), Some(10));
    let current = ext(&evaluator, "TLCGetOrDefault", values(&[string("s:count"), int(0)])).unwrap();
    assert_eq!(current.as_int(), Some(15));
    let stop = operator(|args| Ok(args[1].clone()));
    let args =
        vec![Arg::Value(string("exit")), stop, Arg::Value(Value::TRUE), Arg::Value(Value::FALSE)];
    assert_eq!(ext(&evaluator, "TLCGetAndSet", args).unwrap().as_bool(), Some(false));
    assert!(evaluator.runtime().is_stopped.load(std::sync::atomic::Ordering::SeqCst));
}

#[test]
fn reports_the_unassigned_variables_when_trace_has_no_state() {
    let source = "---- MODULE T ----\nVARIABLES x, y\n====\n";
    let spec = tla_tools_resolve::resolve(source, &mut |_: &str| None).unwrap();
    let evaluator = Evaluator::new(Arc::new(spec), Vec::new());
    assert_eq!(
        ext(&evaluator, "Trace", Vec::new()).unwrap_err().0,
        "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.TupleValue tlc2.module.TLCExt.getTrace(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel) throws java.io.IOException,\nbut it produced the following error:\nIn evaluating TLCExt!Trace, the state is not completely specified yet (variables x, y undefined)."
    );
}

#[test]
fn converts_counter_examples_to_traces() {
    let empty = call("TLCExt", "CounterExample", &[]).unwrap();
    assert_eq!(call("TLCExt", "ToTrace", &[empty]).unwrap().to_string(), "<<>>");
    let state = |n: i32| Value::record(vec![(Symbol::intern("x"), int(n))]);
    let states = Value::set(vec![
        Value::tuple(vec![int(2), state(5)]),
        Value::tuple(vec![int(1), state(4)]),
    ])
    .unwrap();
    let counter_example = Value::record(vec![
        (Symbol::intern("action"), Value::empty_set()),
        (Symbol::intern("state"), states),
    ]);
    let trace = call("TLCExt", "ToTrace", &[counter_example]).unwrap();
    assert_eq!(trace.to_string(), "<<[x |-> 4], [x |-> 5]>>");
    assert_eq!(
        error("TLCExt", "ToTrace", &[tuple(&[])]),
        "The argument of ToTrace should be a CounterExample, but instead it is:\n<<>>"
    );
}

#[test]
fn evaluates_the_simple_operators() {
    assert_eq!(call("TLCExt", "TLCModelValue", &[string("m1")]).unwrap().to_string(), "m1");
    assert!(matches!(call("TLCExt", "TLCModelValue", &[string("m1")]).unwrap(), Value::Model(_)));
    assert_eq!(
        error("TLCExt", "TLCModelValue", &[int(1)]),
        "The argument of ModelValue should be a string, but instead it is:\n1"
    );
    assert_eq!(call("TLCExt", "TLCNoOp", &[int(3)]).unwrap().as_int(), Some(3));
    assert_eq!(call("TLCExt", "TLCCache", &[int(3), tuple(&[])]).unwrap().as_int(), Some(3));
    assert_eq!(call("TLCExt", "TLCDefer", &[int(3)]).unwrap().as_bool(), Some(true));
    // The low 32 bits of tla-ts's getTlcFingerprint([0]), 0xd0ba3e880dcdd983.
    assert_eq!(call("TLCExt", "TLCFP", &[int(0)]).unwrap().as_int(), Some(0x0dcd_d983));
    assert_eq!(
        error("TLCExt", "PickSuccessor", &[Value::TRUE]),
        "PickSuccessor is not supported yet"
    );
}

#[test]
fn rejects_what_tlc_eval_definition_cant_evaluate() {
    let source = "---- MODULE T ----\nF(a) == a\nC == 1\n====\n";
    let spec = tla_tools_resolve::resolve(source, &mut |_: &str| None).unwrap();
    let evaluator = Evaluator::new(Arc::new(spec), Vec::new());
    assert_eq!(
        ext(&evaluator, "TLCEvalDefinition", values(&[string("F")])).unwrap_err().0,
        "The argument of TLCEvalDefinition should be a zero-arity definition, but instead it is:\nF"
    );
    assert_eq!(
        ext(&evaluator, "TLCEvalDefinition", values(&[string("G")])).unwrap_err().0,
        "The argument of TLCEvalDefinition should be a name of a definition reachable from the root module, but instead it is:\n\"G\""
    );
}

#[test]
fn counts_possibilities() {
    let evaluator = evaluator();
    let possible = |name: &str, args: &[Value]| {
        call_in(&evaluator, "_Possible", name, false, values(args)).unwrap()
    };
    possible("_Track", &[Value::TRUE, string("a")]);
    possible("_Track", &[Value::TRUE, string("a")]);
    possible("_Track", &[Value::FALSE, string("b")]);
    let counts = possible("_Counts", &[]);
    assert_eq!(counts.apply(&string("a")).unwrap().as_int(), Some(2));
    assert_eq!(counts.apply(&string("b")).unwrap().as_int(), Some(0));
    assert_eq!(possible("_CheckName", &[string("a")]).as_bool(), Some(true));
    assert_eq!(possible("_CheckName", &[string("b")]).as_bool(), Some(false));
    assert_eq!(evaluator.runtime().output.lock().unwrap().len(), 1);
    let named = ext(&evaluator, "TLCGetOrDefault", values(&[string("s:_possible"), tuple(&[])]));
    assert!(named.unwrap().equals(&counts).unwrap());
}

#[test]
fn asserts_that_an_expression_fails_with_a_message() {
    let evaluator = evaluator();
    let message = |text: &'static str| Arg::Op(Operator::closure(move |_, _| Ok(string(text))));
    let failing = || operator(|_| Err(tla_tools_value::Error("boom".to_owned())));
    let assert_error = |args: Vec<Arg>| ext(&evaluator, "AssertError", args);
    assert_eq!(assert_error(vec![message("boom"), failing()]).unwrap().as_bool(), Some(true));
    assert_eq!(assert_error(vec![message("bang"), failing()]).unwrap().as_bool(), Some(false));
    let holding = operator(|_| Ok(Value::TRUE));
    assert_eq!(assert_error(vec![message("boom"), holding]).unwrap().as_bool(), Some(false));
    // Applied to values, as an operator argument is, the expression has not failed.
    assert_eq!(assert_error(values(&[string("boom"), int(1)])).unwrap().as_bool(), Some(false));
    assert!(
        assert_error(values(&[int(1), int(1)]))
            .unwrap_err()
            .0
            .ends_with("a non-string expression was used as the err of an AssertError(err, exp).")
    );
}

/// The value of each assumption of `body` in a module extending `modules`, once the model
/// checker has started with the options of `config`.
fn assumptions(modules: &str, body: &str, config: &str) -> Vec<Result<Value>> {
    let source = format!("---- MODULE T ----\nEXTENDS {modules}\n{body}\n====\n");
    let spec = tla_tools_resolve::resolve(&source, &mut |_: &str| None).unwrap();
    let assumptions = spec.assumptions.clone();
    let evaluator = Evaluator::new(Arc::new(spec), Vec::new());
    let config = tla_tools_parser::parse_config(config).unwrap();
    evaluator.runtime().start(CheckerOptions::for_config(&config));
    let results = assumptions.into_iter().map(|def| evaluator.eval_def(def, None));
    results.map(|result| result.map_err(|error| tla_tools_value::Error(error.message))).collect()
}

fn holds(results: Vec<Result<Value>>) {
    for (index, result) in results.into_iter().enumerate() {
        assert_eq!(result.map(|value| value.as_bool()), Ok(Some(true)), "assumption {index}");
    }
}

/// TLC's test-model/ModuleSemanticsAssume: Bags reports sums beyond MaxInt as overflows, and
/// RandomSubset reports a negative count, which AssertError catches.
#[test]
fn catches_the_failures_tlcs_module_semantics_model_asserts() {
    let body = r#"
MaxInt == 2147483647
BagCardMax   == BagCardinality([x \in {1, 2} |-> MaxInt]) > MaxInt
BagCupMax    == ([x \in {1} |-> MaxInt] (+) [x \in {1} |-> 1])[1] > MaxInt
BagUnionMax  == BagUnion({[x \in {1} |-> MaxInt], [x \in {1} |-> 2]})[1] > MaxInt
RandomSubsetNegRefl == RandomSubset(-1, {1, 2}) = RandomSubset(-1, {1, 2})
ASSUME BagCardinality([x \in {1, 2} |-> 2]) = 4
ASSUME AssertError("Overflow when computing 2147483647+2147483647", BagCardMax)
ASSUME AssertError("Overflow when computing 2147483647+1", BagCupMax)
ASSUME AssertError("Overflow when computing 2+2147483647", BagUnionMax)
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.Randomization.RandomSubset(tlc2.value.impl.Value,tlc2.value.impl.Value),\nbut it produced the following error:\n-1",
                   RandomSubsetNegRefl)
ASSUME ~AssertError("Overflow", BagCardMax)
ASSUME ~AssertError("Overflow", 1 + 1)
"#;
    holds(assumptions("Bags, Integers, Randomization, TLCExt", body, ""));
}

#[test]
fn defers_and_wraps_what_tlc_hands_expressions() {
    let body = r#"
ASSUME TLCDefer(1 \div 0)
ASSUME AssertError("Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLCGetSet.TLCGetEval(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel),\nbut it produced the following error:\nThe second argument of \\div is 0.",
                   TLCGet(1 \div 0))
"#;
    holds(assumptions("Integers, TLC, TLCExt", body, ""));
}

/// TLC's test-model/suite/test220 and DieHard/DieHardest read the model checker's options.
#[test]
fn reads_the_options_of_the_model_checker_in_assumptions() {
    let body = r#"
ASSUME TLCGet("config").deadlock = FALSE
ASSUME TLCGet("config").mode = "bfs" /\ TLCGet("config").worker = 1
"#;
    holds(assumptions("TLC", body, "CHECK_DEADLOCK FALSE"));
    let deadlock = assumptions("TLC", "ASSUME TLCGet(\"config\").deadlock", "");
    assert_eq!(deadlock[0].clone().map(|value| value.as_bool()), Ok(Some(true)));
}
