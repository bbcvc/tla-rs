//! Resolves small modules from source and evaluates their definitions.

#![allow(dead_code)]

use std::collections::HashMap;
use std::sync::Arc;

use tla_eval::{ConstBinding, EvalError, Evaluator, State, Value};
use tla_resolve::{DefId, RootName, Spec, resolve};

/// The module `Test` with `body` as its units.
pub fn module(body: &str) -> String {
    format!("---- MODULE Test ----\n{body}\n====\n")
}

/// Resolves the module `Test` with `body`, and other modules the loader supplies.
pub fn spec(body: &str, modules: &[(&str, &str)]) -> Spec {
    let modules: HashMap<String, String> =
        modules.iter().map(|(name, source)| (name.to_string(), source.to_string())).collect();
    resolve(&module(body), &mut |name: &str| modules.get(name).cloned())
        .unwrap_or_else(|error| panic!("{error}"))
}

/// An evaluator for the module `Test` with `body`, other modules the loader supplies, and the
/// constants bound in declaration order.
pub fn evaluator_with(
    body: &str,
    modules: &[(&str, &str)],
    constants: Vec<ConstBinding>,
) -> Evaluator {
    Evaluator::new(Arc::new(spec(body, modules)), constants)
}

/// The definition `name` of the root module of `spec`.
pub fn lookup(spec: &Spec, name: &str) -> DefId {
    match spec.lookup(name) {
        Some(RootName::Def(id)) => id,
        other => panic!("{name} is {other:?}"),
    }
}

pub fn evaluator(body: &str) -> Evaluator {
    evaluator_with(body, &[], Vec::new())
}

pub fn def(evaluator: &Evaluator, name: &str) -> DefId {
    lookup(evaluator.spec(), name)
}

pub fn eval(evaluator: &Evaluator, name: &str) -> Result<Value, EvalError> {
    evaluator.eval_def(def(evaluator, name), None)
}

/// TLC's printed form of each named definition of `body`, evaluated as constant expressions.
pub fn show(body: &str, names: &[&str]) -> Vec<String> {
    let evaluator = evaluator(body);
    names
        .iter()
        .map(|name| match eval(&evaluator, name) {
            Ok(value) => value.to_string(),
            Err(error) => panic!("{name}: {error}"),
        })
        .collect()
}

/// The value of `expr` as a constant expression, printed as TLC prints it.
pub fn value(expr: &str) -> String {
    show(&format!("Expr == {expr}"), &["Expr"]).remove(0)
}

/// The error evaluating `expr` as a constant expression.
pub fn error(expr: &str) -> EvalError {
    let evaluator = evaluator(&format!("Expr == {expr}"));
    match eval(&evaluator, "Expr") {
        Ok(value) => panic!("{expr} evaluated to {value}"),
        Err(error) => error,
    }
}

pub fn state(values: Vec<Value>) -> State {
    values.into()
}

pub fn int(value: i32) -> Value {
    Value::Int(value)
}

pub fn ints(values: &[i32]) -> Value {
    Value::set(values.iter().map(|&value| Value::Int(value)).collect()).unwrap()
}
