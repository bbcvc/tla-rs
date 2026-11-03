//! Native implementations of TLC's standard modules, ported from tla-ts.
//!
//! TLC replaces the placeholder definitions of its standard modules with Java methods, and
//! [`lookup`] gives the native that replaces each one here. A definition TLC evaluates from its
//! TLA+ source, such as `LOCAL Sum` of Bags or anything in Reals, has no native.
//!
//! TLC reports a failure inside an operator's Java method as a failure of that method, unless the
//! method raises it itself as an `EvalException`. Natives keep the two kinds apart with
//! [`Failure`], and [`java!`] wraps the second kind in TLC's message for operators TLC implements
//! with such a method.

use std::sync::Arc;

use tla_value::{Error, LazySet, Value};

use crate::{Arg, Native};

/// A failure of a native operator.
pub(crate) enum Failure {
    /// An error the operator's Java code raises itself, which TLC reports as it is.
    Module(Error),
    /// An error evaluation raises underneath the operator, which TLC reports as a failure of the
    /// Java method that overrides the operator.
    Eval(Error),
}

impl From<Error> for Failure {
    fn from(error: Error) -> Self {
        Self::Eval(error)
    }
}

impl Failure {
    pub(crate) fn into_error(self) -> Error {
        match self {
            Self::Module(error) | Self::Eval(error) => error,
        }
    }

    /// The error TLC reports when this fails inside the Java method `signature`.
    fn in_java(self, signature: &str) -> Error {
        match self {
            Self::Module(error) => error,
            Self::Eval(error) => java_error(signature, &error.0),
        }
    }
}

/// What a native computes: a value, or a [`Failure`].
pub(crate) type Outcome<T = Value> = std::result::Result<T, Failure>;

/// Fails with a [`Failure::Module`] formatted like `format!`.
macro_rules! fail {
    ($($arg:tt)*) => {
        return Err($crate::stdlib::Failure::Module(tla_value::Error(format!($($arg)*))))
    };
}

/// Fails with a [`Failure::Eval`] formatted like `format!`.
macro_rules! fail_eval {
    ($($arg:tt)*) => {
        return Err($crate::stdlib::Failure::Eval(tla_value::Error(format!($($arg)*))))
    };
}

/// The [`Native`] of an operator whose failures TLC reports as they are.
macro_rules! native {
    ($operator:expr) => {{
        fn native(ctx: &mut $crate::Ctx<'_>, args: &[$crate::Arg]) -> tla_value::Result<Value> {
            $operator(ctx, args).map_err($crate::stdlib::Failure::into_error)
        }
        native as $crate::Native
    }};
}

/// The [`Native`] of an operator TLC implements with the Java method `signature`.
macro_rules! java {
    ($operator:expr, $signature:expr) => {{
        fn native(ctx: &mut $crate::Ctx<'_>, args: &[$crate::Arg]) -> tla_value::Result<Value> {
            $operator(ctx, args).map_err(|failure| failure.in_java($signature))
        }
        native as $crate::Native
    }};
}

/// The [`Native`] of an operator that needs what natives don't get, such as unevaluated
/// arguments or the model checker's state.
macro_rules! unsupported {
    ($name:literal) => {{
        fn native(_: &mut $crate::Ctx<'_>, _: &[$crate::Arg]) -> tla_value::Result<Value> {
            Err(tla_value::Error(concat!($name, " is not supported yet").to_owned()))
        }
        native as $crate::Native
    }};
}

mod bags;
mod finite_sets;
mod naturals;
mod randomization;
mod sequences;
pub(crate) mod tlc;
mod tlc_ext;

/// The native implementation of `name` in standard module `module`. TLC overrides the arithmetic
/// of Naturals with that of Integers when the spec loads Integers anywhere.
pub(crate) fn lookup(module: &str, name: &str, uses_integers: bool) -> Option<Native> {
    match module {
        "Naturals" => naturals::lookup(name, uses_integers),
        "Integers" => naturals::lookup_integers(name),
        "Sequences" => sequences::lookup(name),
        "FiniteSets" => finite_sets::lookup(name),
        "TLC" => tlc::lookup(name),
        "TLCExt" => tlc_ext::lookup(name),
        "_Possible" => tlc_ext::lookup_possible(name),
        "Bags" => bags::lookup(name, uses_integers),
        "Randomization" => randomization::lookup(name),
        _ => None,
    }
}

/// Argument `index`, which must be a value.
fn arg(args: &[Arg], index: usize) -> Outcome<&Value> {
    match args.get(index) {
        Some(arg) => Ok(arg.value()?),
        None => fail_eval!("Expected a value as argument {}", index + 1),
    }
}

/// Argument `index`, which must be an operator.
fn op_arg(args: &[Arg], index: usize) -> Outcome<&crate::Operator> {
    match args.get(index) {
        Some(arg) => Ok(arg.op()?),
        None => fail_eval!("Expected an operator as argument {}", index + 1),
    }
}

/// TLC's message for a failure inside the Java method `signature`.
fn java_error(signature: &str, message: &str) -> Error {
    Error(format!(
        "Attempted to apply the operator overridden by the Java method\n{signature},\nbut it produced the following error:\n{message}"
    ))
}

/// TLC's `EC.TLC_MODULE_ARGUMENT_ERROR`.
fn argument_error(position: &str, name: &str, expected: &str, value: &Value) -> Failure {
    Failure::Module(Error(format!(
        "The {position} argument of {name} should be a {expected}, but instead it is:\n{value}"
    )))
}

/// The Java class TLC represents a value with, as its errors name it.
fn java_class(value: &Value) -> &'static str {
    match value {
        Value::Bool(_) => "BoolValue",
        Value::Int(_) => "IntValue",
        Value::Str(_) => "StringValue",
        Value::Model(_) => "ModelValue",
        Value::Set(_) | Value::MixedSet(_) => "SetEnumValue",
        Value::Interval(..) => "IntervalValue",
        Value::Tuple(_) => "TupleValue",
        Value::Func(func) if func.keys.iter().all(|key| matches!(key, Value::Str(_))) => {
            "RecordValue"
        }
        Value::Func(_) => "FcnRcdValue",
        Value::LazyFunc(_) => "FcnLambdaValue",
        Value::Lazy(set) => match **set {
            LazySet::Subset(_) => "SubsetValue",
            LazySet::FuncSet { .. } => "SetOfFcnsValue",
            LazySet::RecordSet(_) => "SetOfRcdsValue",
            LazySet::Product(_) => "SetOfTuplesValue",
            LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => {
                "UserValue"
            }
            LazySet::Cup(..) => "SetCupValue",
            LazySet::Cap(..) => "SetCapValue",
            LazySet::Minus(..) => "SetDiffValue",
            LazySet::Filtered { .. } => "SetPredValue",
            LazySet::Union(_) => "UnionValue",
        },
    }
}

/// Whether TLC implements this set with a Java class of its own, which it can't enumerate.
fn is_overridden_set(value: &Value) -> bool {
    matches!(value, Value::Lazy(set) if matches!(
        **set,
        LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any
    ))
}

/// The elements of a sequence, or `None` if the value is not one. A function TLC doesn't
/// enumerate is enumerated first.
fn sequence_elements(value: &Value) -> Outcome<Option<Arc<[Value]>>> {
    match value {
        Value::Tuple(items) => Ok(Some(items.clone())),
        Value::LazyFunc(_) => match value.materialize()? {
            Value::Tuple(items) => Ok(Some(items)),
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

/// The pairs of a finite function, in key order.
fn function_pairs(function: &Value) -> Outcome<Vec<(Value, Value)>> {
    match function {
        Value::Tuple(items) => Ok(items
            .iter()
            .enumerate()
            .map(|(index, item)| (Value::Int(index as i32 + 1), item.clone()))
            .collect()),
        Value::Func(func) => {
            Ok(func.keys.iter().cloned().zip(func.values.iter().cloned()).collect())
        }
        _ => fail_eval!("Attempted to enumerate {function}, which is not a finite function"),
    }
}

/// Fails unless `value` is a set the operator `name` can enumerate. TLC evaluates some operators
/// in its core, where a wrong argument is a failure of evaluation rather than of the operator.
fn check_enumerable(value: &Value, name: &str, is_core: bool) -> Outcome<()> {
    let failure = |message: String| {
        if is_core { Failure::Eval(Error(message)) } else { Failure::Module(Error(message)) }
    };
    if !value.is_set() {
        return Err(failure(format!("{name} expects a set but received {value}")));
    }
    if !value.is_enumerable() {
        return Err(failure(format!("{name} cannot enumerate the non-enumerable set {value}")));
    }
    Ok(())
}

/// The elements of a set the operator `name` enumerates.
fn enumerable_elements(value: &Value, name: &str, is_core: bool) -> Outcome<Arc<[Value]>> {
    check_enumerable(value, name, is_core)?;
    Ok(value.elements()?)
}

/// The set of `elements`, failing as TLC does when it can't sort them.
fn sorted_set(elements: Vec<Value>) -> Outcome {
    let set = Value::set(elements)?;
    if matches!(set, Value::MixedSet(_)) {
        return Ok(Value::Set(set.elements()?));
    }
    Ok(set)
}

/// The kind of a value as some of TLC's errors name it, which calls every function a function.
fn kind_name(value: &Value) -> &'static str {
    match value {
        Value::Bool(_) => "boolean",
        Value::Int(_) => "integer",
        Value::Str(_) => "string",
        Value::Model(_) => "model value",
        _ if value.is_set() => "set",
        _ => "function",
    }
}

#[cfg(test)]
pub(crate) mod testing {
    //! Calls natives in an evaluator for an empty module.

    use std::sync::Arc;

    use tla_value::{Result, Value};

    use crate::{Arg, Ctx, Evaluator, Operator};

    pub fn evaluator() -> Evaluator {
        let spec = tla_resolve::resolve("---- MODULE T ----\n====\n", &mut |_: &str| None)
            .expect("an empty module resolves");
        Evaluator::new(Arc::new(spec), Vec::new())
    }

    /// Calls `module!name` with value arguments, with the arithmetic of Integers if
    /// `uses_integers`.
    pub fn call_in(
        evaluator: &Evaluator,
        module: &str,
        name: &str,
        uses_integers: bool,
        args: Vec<Arg>,
    ) -> Result<Value> {
        let native = super::lookup(module, name, uses_integers)
            .unwrap_or_else(|| panic!("{module}!{name} has no native"));
        native(&mut Ctx::new(evaluator, None), &args)
    }

    pub fn call(module: &str, name: &str, args: &[Value]) -> Result<Value> {
        let args = args.iter().cloned().map(Arg::Value).collect();
        call_in(&evaluator(), module, name, false, args)
    }

    /// The message of the error `module!name` fails with.
    pub fn error(module: &str, name: &str, args: &[Value]) -> String {
        match call(module, name, args) {
            Ok(value) => panic!("{module}!{name} returned {value} instead of failing"),
            Err(error) => error.0,
        }
    }

    pub fn int(value: i32) -> Value {
        Value::Int(value)
    }

    pub fn ints(values: &[i32]) -> Value {
        Value::set(values.iter().copied().map(Value::Int).collect()).unwrap()
    }

    pub fn tuple(values: &[i32]) -> Value {
        Value::tuple(values.iter().copied().map(Value::Int).collect())
    }

    pub fn string(text: &str) -> Value {
        Value::str(text)
    }

    pub fn operator(apply: fn(&[Value]) -> Result<Value>) -> Arg {
        Arg::Op(Operator::closure(move |_, args| apply(args)))
    }
}
