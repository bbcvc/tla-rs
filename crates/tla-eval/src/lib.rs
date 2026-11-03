//! Evaluates the expressions of a resolved specification.
//!
//! An [`Evaluator`] holds a [`Spec`], the values the model configuration gives its constants,
//! and the native implementations that replace the placeholder definitions of TLC's standard
//! modules, as TLC's Java overrides replace them. Expressions are evaluated in a chain of
//! frames (see [`tla_resolve::Scope`]), with an optional current state and next state.

mod config;
mod env;
mod eval;
mod native;
mod runtime;
mod stdlib;

use std::sync::Arc;

pub use config::{Model, bind_model, config_value};
pub use native::{Arg, Ctx, Native, Operator};
pub use runtime::{CheckerOptions, Registers, Runtime, Statistics};
use tla_ast::{Span, Symbol};
use tla_resolve::{DefId, ModuleId, Spec};
pub use tla_value::{self as value, Value};

/// An evaluation error at a place in a module.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("{message}\nline {line}, column {column} of module {module}")]
pub struct EvalError {
    pub message: String,
    pub module: Symbol,
    pub span: Span,
    pub line: usize,
    pub column: usize,
}

impl EvalError {
    pub(crate) fn at(
        spec: &Spec,
        module: ModuleId,
        span: Span,
        message: impl Into<String>,
    ) -> Self {
        let info = &spec.modules[module.index()];
        let (line, column) = span.line_column(&info.source);
        Self { message: message.into(), module: info.name, span, line, column }
    }
}

pub type Result<T> = std::result::Result<T, EvalError>;

/// What a declared constant stands for in a model.
#[derive(Clone)]
pub enum ConstBinding {
    /// `N = 3` in the configuration.
    Value(Value),
    /// `N <- Def` in the configuration: the constant is replaced by a definition of the root
    /// module.
    Def(DefId),
}

/// The variables of one state, by [`tla_resolve::VarId`].
pub type State = Arc<[Value]>;

/// A handle to an evaluator. Clones share the specification, the constants, and the runtime, so
/// that lazy values can keep the evaluator they need.
#[derive(Clone)]
pub struct Evaluator {
    pub(crate) spec: Arc<Spec>,
    /// By [`tla_resolve::ConstId`].
    pub(crate) constants: Arc<[ConstBinding]>,
    /// The native implementation of each definition TLC overrides, by [`DefId`].
    pub(crate) natives: Arc<[Option<Native>]>,
    /// Whether the native of each definition takes its arguments unevaluated, as the Java methods
    /// TLC hands expressions do, by [`DefId`].
    pub(crate) takes_expressions: Arc<[bool]>,
    /// What the configuration replaces each definition with, by [`DefId`].
    pub(crate) overrides: Arc<[Option<ConstBinding>]>,
    pub(crate) runtime: Arc<Runtime>,
    /// Whether each definition is a function definition that refers to itself, by [`DefId`].
    pub(crate) is_recursive: Arc<[bool]>,
}

impl Evaluator {
    pub fn new(spec: Arc<Spec>, constants: Vec<ConstBinding>) -> Self {
        let uses_integers = spec
            .modules
            .iter()
            .any(|module| module.is_standard && module.name.as_str() == "Integers");
        let natives = spec
            .defs
            .iter()
            .map(|def| {
                let module = &spec.modules[def.module.index()];
                let is_overridable = tla_resolve::is_standard_module(module.name.as_str());
                is_overridable
                    .then(|| stdlib::lookup(module.name.as_str(), def.name.as_str(), uses_integers))
                    .flatten()
            })
            .collect();
        let takes_expressions = spec
            .defs
            .iter()
            .map(|def| {
                let module = spec.modules[def.module.index()].name.as_str();
                tla_resolve::is_standard_module(module)
                    && stdlib::takes_expressions(module, def.name.as_str())
            })
            .collect();
        let overrides = vec![None; spec.defs.len()].into();
        let is_recursive = eval::recursive_functions(&spec).into();
        Self {
            spec,
            constants: constants.into(),
            natives,
            takes_expressions,
            overrides,
            runtime: Arc::default(),
            is_recursive,
        }
    }

    /// Replaces definitions with the values or definitions the configuration gives them.
    pub fn with_overrides(mut self, overrides: Vec<(DefId, ConstBinding)>) -> Self {
        let mut replaced = self.overrides.to_vec();
        for (def, binding) in overrides {
            replaced[def.index()] = Some(binding);
        }
        self.overrides = replaced.into();
        self
    }

    pub fn spec(&self) -> &Spec {
        &self.spec
    }

    pub fn runtime(&self) -> &Runtime {
        &self.runtime
    }

    /// Evaluates a definition without parameters, such as an `ASSUME` or `Init`, in `state`, or
    /// as a constant expression when there is no state.
    pub fn eval_def(&self, def: DefId, state: Option<&State>) -> Result<Value> {
        self.eval_zero_arity(def, state, None)
    }

    /// Evaluates a definition without parameters, such as an action or an action property, on
    /// the step from `state` to `next`, which primed expressions read.
    pub fn eval_action(&self, def: DefId, state: &State, next: &State) -> Result<Value> {
        self.eval_zero_arity(def, Some(state), Some(next))
    }
}
