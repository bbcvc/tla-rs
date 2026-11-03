//! The interface between the evaluator and native implementations of standard modules.

use std::sync::Arc;

use tla_resolve::{Builtin, DefId};
use tla_value::{Error, Result, Value};

use crate::env::Frame;
use crate::{Evaluator, State};

/// A native implementation of a standard module's operator. It receives its arguments
/// evaluated, and an operator for each parameter that takes one, such as `Test(_)` of
/// `SelectSeq`.
pub type Native = fn(&mut Ctx<'_>, &[Arg]) -> Result<Value>;

pub enum Arg {
    Value(Value),
    Op(Operator),
}

impl Arg {
    pub fn value(&self) -> Result<&Value> {
        match self {
            Arg::Value(value) => Ok(value),
            Arg::Op(_) => Err(Error("Expected a value but found an operator".to_owned())),
        }
    }

    pub fn op(&self) -> Result<&Operator> {
        match self {
            Arg::Op(op) => Ok(op),
            Arg::Value(value) => Err(Error(format!("Expected an operator but found {value}"))),
        }
    }
}

/// An operator passed as an argument.
#[derive(Clone)]
pub struct Operator(pub(crate) OperatorKind);

#[derive(Clone)]
pub(crate) enum OperatorKind {
    /// A definition, with the frame it captures.
    Def {
        def: DefId,
        parent: Option<Arc<Frame>>,
    },
    Builtin(Builtin),
    /// An operator implemented in Rust.
    Closure(Arc<RustOperator>),
}

type RustOperator = dyn Fn(&mut Ctx<'_>, &[Value]) -> Result<Value> + Send + Sync;

impl Operator {
    /// An operator implemented by a Rust closure, for natives and tests.
    pub fn closure(
        apply: impl Fn(&mut Ctx<'_>, &[Value]) -> Result<Value> + Send + Sync + 'static,
    ) -> Self {
        Self(OperatorKind::Closure(Arc::new(apply)))
    }
}

/// What a native can use of the evaluator: operators passed to it, the state, and TLC's runtime.
pub struct Ctx<'a> {
    pub(crate) evaluator: &'a Evaluator,
    pub(crate) state: Option<&'a State>,
    /// The next state, which an operator argument reads when it primes an expression.
    pub(crate) next: Option<&'a State>,
}

impl<'a> Ctx<'a> {
    pub(crate) fn new(evaluator: &'a Evaluator, state: Option<&'a State>) -> Self {
        Self { evaluator, state, next: None }
    }

    /// Applies an operator argument to `args`.
    pub fn call(&mut self, op: &Operator, args: &[Value]) -> Result<Value> {
        self.evaluator.apply_operator(op, args, self.state, self.next)
    }

    pub fn runtime(&self) -> &crate::Runtime {
        &self.evaluator.runtime
    }

    /// The current state, when evaluating in one.
    pub fn state(&self) -> Option<&State> {
        self.state
    }
}
