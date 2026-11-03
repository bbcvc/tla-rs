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

use std::collections::HashSet;
use std::sync::{Arc, OnceLock};

pub use config::{Model, OperatorTable, bind_model, config_value};
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
    /// `F(1) = 2  F(2) = 3` in the configuration: an operator defined by its values.
    Table(Arc<OperatorTable>),
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
    /// Whether each definition is a constant TLC computes once, by [`DefId`], and its value once
    /// computed.
    pub(crate) is_constant_definition: Arc<[bool]>,
    pub(crate) constant_values: Arc<[OnceLock<Value>]>,
    /// TLC's `TLCEval`, and the applications of it whose argument TLC normalizes, by address.
    pub(crate) tlc_eval: Option<DefId>,
    pub(crate) normalizing_evaluations: Arc<HashSet<usize>>,
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
                let module = spec.modules[def.module.index()].name.as_str();
                stdlib::lookup(module, def.name.as_str(), uses_integers)
            })
            .collect();
        let takes_expressions = spec
            .defs
            .iter()
            .map(|def| {
                let module = spec.modules[def.module.index()].name.as_str();
                stdlib::takes_expressions(module, def.name.as_str())
            })
            .collect();
        let overrides = vec![None; spec.defs.len()].into();
        let is_recursive = eval::recursive_functions(&spec).into();
        let is_constant_definition = eval::constant_definitions(&spec).into();
        let constant_values = (0..spec.defs.len()).map(|_| OnceLock::new()).collect();
        let tlc_eval = eval::tlc_eval(&spec);
        let normalizing_evaluations = Arc::new(
            tlc_eval.map(|def| eval::normalizing_evaluations(&spec, def)).unwrap_or_default(),
        );
        Self {
            spec,
            constants: constants.into(),
            natives,
            takes_expressions,
            overrides,
            runtime: Arc::default(),
            is_recursive,
            is_constant_definition,
            constant_values,
            tlc_eval,
            normalizing_evaluations,
        }
    }

    /// Replaces the definitions of the community modules tla-rs implements, IOUtils for now, with
    /// natives, as TLC does when CommunityModules' `CommunityModules-deps.jar` is on its class
    /// path. Without it, TLC evaluates their TLA+ definitions, most of which are placeholders.
    pub fn with_community_modules(mut self) -> Self {
        let mut natives = self.natives.to_vec();
        for (index, def) in self.spec.defs.iter().enumerate() {
            let module = self.spec.modules[def.module.index()].name.as_str();
            if def.depth == 0
                && let Some(native) = stdlib::lookup_community(module, def.name.as_str())
            {
                natives[index] = Some(native);
            }
        }
        self.natives = natives.into();
        self
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
