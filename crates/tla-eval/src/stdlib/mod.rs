//! Native implementations of TLC's standard modules, ported from tla-ts.
//!
//! TLC replaces the placeholder definitions of its standard modules with Java methods, and
//! [`lookup`] gives the native that replaces each one here. A definition TLC evaluates from its
//! TLA+ source, such as `LOCAL Sum` of Bags or anything in Reals, has no native.
//!
//! TLC reports a failure inside an operator's Java method as a failure of that method, unless the
//! method raises it itself as an `EvalException`. Natives keep the two kinds apart with
//! [`Failure`].

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
    fn into_error(self) -> Error {
        match self {
            Self::Module(error) | Self::Eval(error) => error,
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

mod naturals;

/// The native implementation of `name` in standard module `module`. TLC overrides the arithmetic
/// of Naturals with that of Integers when the spec loads Integers anywhere.
pub(crate) fn lookup(module: &str, name: &str, uses_integers: bool) -> Option<Native> {
    match module {
        "Naturals" => naturals::lookup(name, uses_integers),
        "Integers" => naturals::lookup_integers(name),
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

/// TLC's message for a failure inside the Java method `signature`.
fn java_error(signature: &str, message: &str) -> Error {
    Error(format!(
        "Attempted to apply the operator overridden by the Java method\n{signature},\nbut it produced the following error:\n{message}"
    ))
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

#[cfg(test)]
pub(crate) mod testing {
    //! Calls natives in an evaluator for an empty module.

    use std::sync::Arc;

    use tla_value::{Result, Value};

    use crate::{Arg, Ctx, Evaluator};

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

    pub fn string(text: &str) -> Value {
        Value::str(text)
    }
}
