//! Evaluates the expressions of a resolved specification.
//!
//! An [`Evaluator`] holds a [`Spec`], the values the model configuration gives its constants,
//! and the native implementations that replace the placeholder definitions of TLC's standard
//! modules, as TLC's Java overrides replace them. Expressions are evaluated in a chain of
//! frames (see [`tla_resolve::Scope`]), with an optional current state and next state.

mod config;
mod env;
mod eval;
mod java;
mod native;
mod runtime;
mod stdlib;

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex, OnceLock};

pub use config::{Model, OperatorTable, bind_model, config_value};
pub use eval::NextAction;
pub use java::{JavaOverrideError, java_overrides};
pub use native::{Arg, Ctx, Native, Operator};
pub use runtime::{CheckerOptions, Registers, Runtime, Statistics};
pub use stdlib::tlc::tlc_fingerprint;
use tla_ast::{Span, Symbol};
use tla_resolve::{DefId, ModuleId, Spec, VarId};
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
    /// The state, when an initial predicate or an action leaves variables of it unassigned,
    /// which TLC reports with the partial state.
    pub incomplete: Option<Box<Incomplete>>,
}

/// A state an initial predicate or an action leaves with variables unassigned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Incomplete {
    /// The action that assigned the next state, as TLC names it, or `None` for an initial state.
    pub action: Option<Symbol>,
    /// The variables left unassigned.
    pub missing: Vec<VarId>,
    /// The value of each variable as TLC prints it, or `None` where it is unassigned.
    pub state: Vec<Option<String>>,
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
        Self { message: message.into(), module: info.name, span, line, column, incomplete: None }
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
    /// The function constructors that apply the recursive function whose body holds them, by
    /// address, which TLC builds lazily.
    pub(crate) recursive_constructions: Arc<HashSet<usize>>,
    /// What TLC's ENABLED does with the variables of an instantiated module.
    pub(crate) instance_enabled: Arc<eval::InstanceEnabled>,
    /// Whether each definition is a constant TLC computes once, by [`DefId`], and its value once
    /// computed.
    pub(crate) is_constant_definition: Arc<[bool]>,
    pub(crate) constant_values: Arc<[OnceLock<Value>]>,
    /// TLC's `TLCEval`, and the applications of it whose argument TLC normalizes, by address.
    pub(crate) tlc_eval: Option<DefId>,
    pub(crate) normalizing_evaluations: Arc<HashSet<usize>>,
    /// TLCExt's `TLCCache`, whose Java override caches the value of its expression.
    pub(crate) tlc_cache: Option<DefId>,
    /// TLC's split of each next-state relation split so far into actions.
    pub(crate) next_actions: Arc<Mutex<HashMap<DefId, Arc<[NextAction]>>>>,
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
        let recursive_constructions = Arc::new(eval::recursive_constructions(&spec));
        let instance_enabled = Arc::new(eval::instance_enabled(&spec));
        let is_constant_definition = eval::constant_definitions(&spec).into();
        let constant_values = (0..spec.defs.len()).map(|_| OnceLock::new()).collect();
        let tlc_eval = eval::tlc_eval(&spec);
        let tlc_cache = spec.defs.iter().position(|def| {
            let module = spec.modules[def.module.index()].name.as_str();
            module == "TLCExt" && def.name.as_str() == "TLCCache"
        });
        let tlc_cache = tlc_cache.map(|index| DefId(index as u32));
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
            recursive_constructions,
            instance_enabled,
            is_constant_definition,
            constant_values,
            tlc_eval,
            normalizing_evaluations,
            tlc_cache,
            next_actions: Arc::default(),
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

    /// Whether a string with a character above U+00FF can reach a state: one the spec writes or
    /// the configuration binds, or one a JSON deserializer reads. TLC fingerprints a string by
    /// the low byte of each character, so it counts states whose strings differ only above U+00FF
    /// as one, and a checker that counts states as TLC does fingerprints them with
    /// [`tlc_fingerprint`] (tla-ts `hasWideString`).
    pub fn has_wide_strings(&self) -> bool {
        fn is_wide_value(value: &Value) -> bool {
            match value {
                Value::Str(text) => eval::is_wide(text.as_str()),
                Value::Set(elements) | Value::MixedSet(elements) => {
                    elements.iter().any(is_wide_value)
                }
                _ => false,
            }
        }
        let is_wide_binding = |binding: &ConstBinding| match binding {
            ConstBinding::Value(value) => is_wide_value(value),
            ConstBinding::Table(table) => {
                table.rows.iter().any(|(args, value)| args.iter().chain([value]).any(is_wide_value))
            }
            ConstBinding::Def(_) => false,
        };
        self.constants.iter().any(is_wide_binding)
            || self.overrides.iter().flatten().any(is_wide_binding)
            || eval::has_wide_string_literal(&self.spec)
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

    /// Each state satisfying the conjunction of the zero-arity definitions `init`, in TLC's
    /// order, repeats included. `found` returns `Ok(false)` to stop the enumeration.
    pub fn init_states(
        &self,
        init: &[DefId],
        found: &mut dyn FnMut(State) -> Result<bool>,
    ) -> Result<()> {
        self.enumerate_init(init, found)
    }

    /// Each successor of `state` under the zero-arity action definition `next`, in TLC's order,
    /// repeats included, as TLC counts them in "states generated". `found` returns `Ok(false)` to
    /// stop the enumeration.
    pub fn next_states(
        &self,
        next: DefId,
        state: &State,
        found: &mut dyn FnMut(State) -> Result<bool>,
    ) -> Result<()> {
        self.enumerate_next(next, state, found)
    }

    /// TLC's split of the zero-arity action definition `next` into the actions it names in a
    /// behavior (`Tool.getActions`), in TLC's order: the disjuncts of the relation, one action
    /// for each witness of an `\E` over a set TLC computes as a constant, and the bodies of the
    /// definitions it calls with constant arguments. TLC computes the split once, when it
    /// starts, and so does the evaluator, which keeps it for later calls.
    ///
    /// A report of a successor the relation leaves incomplete names the action when there are
    /// several: [`Incomplete::action`] is the [`NextAction::name`] of the one that left it.
    pub fn next_actions(&self, next: DefId) -> Result<Arc<[NextAction]>> {
        self.split_next(next)
    }

    /// Each successor of `state` under one action of a split of the next-state relation, in
    /// TLC's order, repeats included.
    pub fn action_states(
        &self,
        action: &NextAction,
        state: &State,
        found: &mut dyn FnMut(State) -> Result<bool>,
    ) -> Result<()> {
        self.enumerate_action(action, state, found)
    }

    /// Where TLC says an action is, as it labels a step of a behavior (`Action.getLocation`):
    /// `A(1) line 4, col 7 to line 4, col 12 of module M`.
    pub fn action_label(&self, action: &NextAction) -> String {
        self.label_action(action)
    }
}
