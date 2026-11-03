//! One enumeration of states: what it computes, the state it assigns, and where it reports the
//! states it finds.

use std::sync::Arc;

use tla_resolve::{DefBody, DefId, Expr, VarId};
use tla_value::{Symbol, Value};

use super::{Action, Rest, Site};
use crate::env::{Env, Frame, StateRef, Version};
use crate::{EvalError, Evaluator, Incomplete, Result, State};

/// What TLC computes when it walks a predicate.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Computation {
    Init,
    Next,
    Enabled,
}

impl Computation {
    /// What TLC says it was computing when it fails.
    pub fn name(self) -> &'static str {
        match self {
            Computation::Init => "initial states",
            Computation::Next => "next states",
            Computation::Enabled => "ENABLED",
        }
    }
}

pub(crate) struct Run<'r> {
    pub computation: Computation,
    /// The state an action starts from.
    pub current: Option<&'r State>,
    /// The state being assigned: the initial state, or the next state of an action. Branches
    /// assign its variables in place and undo them when they return.
    pub assigned: Vec<Option<Value>>,
    pub unassigned: usize,
    /// Which values `assigned` holds, so that a thunk caches its value for as long as they last.
    version: Version,
    /// The number of versions made so far.
    versions: u64,
    pub is_stopped: bool,
    /// The definition being enumerated, where an incomplete state is reported.
    def: DefId,
    found: Option<&'r mut dyn FnMut(State) -> Result<bool>>,
}

impl<'r> Run<'r> {
    pub(super) fn new(
        evaluator: &Evaluator,
        computation: Computation,
        current: Option<&'r State>,
        def: DefId,
        found: Option<&'r mut dyn FnMut(State) -> Result<bool>>,
    ) -> Self {
        let variables = evaluator.spec.variables.len();
        Self {
            computation,
            current,
            assigned: vec![None; variables],
            unassigned: variables,
            version: Version::first(),
            versions: 0,
            is_stopped: false,
            def,
            found,
        }
    }

    /// The states expressions read: an initial predicate reads the state it assigns, and an
    /// action reads the current state and the next state it assigns.
    pub fn views(&self) -> (Option<StateRef<'_>>, Option<StateRef<'_>>) {
        let assigned = StateRef::Partial(&self.assigned, self.version);
        match self.computation {
            Computation::Init => (Some(assigned), None),
            Computation::Next | Computation::Enabled => {
                (self.current.map(StateRef::Complete), Some(assigned))
            }
        }
    }

    pub fn is_complete(&self) -> bool {
        self.unassigned == 0
    }

    /// Assigns `value` to variable `var` for the rest of the walk, `then`, and undoes it after.
    pub fn with_assigned(
        &mut self,
        var: usize,
        value: Value,
        then: impl FnOnce(&mut Self) -> Result<()>,
    ) -> Result<()> {
        self.assigned[var] = Some(value);
        self.unassigned -= 1;
        self.versions += 1;
        let version = self.version;
        self.version = version.at(self.versions);
        let result = then(self);
        self.assigned[var] = None;
        self.unassigned += 1;
        self.version = version;
        result
    }
}

/// Builds an [`Env`] for an expression of `site` that reads the states of `run`.
pub(super) fn env<'a>(site: &Site, run: &'a Run<'_>) -> Env<'a> {
    let (state, next) = run.views();
    Env { frame: site.frame.clone(), module: site.module, state, next, keep_lazy: false }
}

impl Evaluator {
    /// Each state satisfying the conjunction of the zero-arity definitions `init`, in TLC's
    /// order, repeats included. `found` returns `Ok(false)` to stop the enumeration.
    pub(crate) fn enumerate_init(
        &self,
        init: &[DefId],
        found: &mut dyn FnMut(State) -> Result<bool>,
    ) -> Result<()> {
        let Some(&first) = init.first() else { return Ok(()) };
        let mut run = Run::new(self, Computation::Init, None, first, Some(found));
        self.resume(&mut run, Action::default(), &Rest::Defs { defs: init, rest: &Rest::Done })
    }

    /// Each successor of `state` under the zero-arity action definition `next`, in TLC's order,
    /// repeats included. `found` returns `Ok(false)` to stop the enumeration.
    pub(crate) fn enumerate_next(
        &self,
        next: DefId,
        state: &State,
        found: &mut dyn FnMut(State) -> Result<bool>,
    ) -> Result<()> {
        let mut run = Run::new(self, Computation::Next, Some(state), next, Some(found));
        let defs = [next];
        self.resume(&mut run, Action::default(), &Rest::Defs { defs: &defs, rest: &Rest::Done })
    }

    /// `ENABLED action`: whether the action, evaluated where `env` is, has a successor of the
    /// state `env` reads. TLC stops at the first successor, and doesn't require it complete.
    pub(crate) fn is_enabled(&self, action: &Expr, expr: &Expr, env: &Env<'_>) -> Result<bool> {
        let Some(state) = env.state.and_then(StateRef::complete) else {
            let message = format!("ENABLED needs a complete state at {}", self.location(env, expr));
            return Err(self.error(env, expr, message));
        };
        let def = DefId(0);
        let mut run = Run::new(self, Computation::Enabled, Some(state), def, None);
        let site = Site { frame: env.frame.clone(), module: env.module };
        self.act(action, &site, &mut run, Action::default(), &Rest::Done)?;
        Ok(run.is_stopped)
    }

    /// Starts the walk of the zero-arity definition `def`, which a predicate or an action
    /// conjoins, with `rest` after it.
    pub(super) fn enter_definition(
        &self,
        def: DefId,
        run: &mut Run<'_>,
        action: Action,
        rest: &Rest<'_>,
    ) -> Result<()> {
        if let Some(error) = self.zero_arity_problem(def) {
            return Err(error);
        }
        // The walk enters the definition the configuration replaces `def` with, as TLC does.
        if let Some(target) = self.walked(def, 0) {
            let info = self.spec.def(target);
            let site = Site {
                frame: Arc::new(Frame::new(Vec::new(), info.frame_size, None)),
                module: info.module,
            };
            let DefBody::Expr(body) = &info.body else { unreachable!("a walked definition") };
            return self.act(body, &site, run, action.called(info.name), rest);
        }
        let info = self.spec.def(def);
        let action = action.called(info.name);
        let (state, next) = run.views();
        let value = self.call_def(def, None, Vec::new(), state, next)?;
        if value.as_bool().ok_or_else(|| {
            let message = format!(
                "In computing {}, TLC expected a boolean expression,\nbut instead found {value}.",
                run.computation.name()
            );
            EvalError::at(&self.spec, info.module, info.span, message)
        })? {
            self.resume(run, action, rest)
        } else {
            Ok(())
        }
    }

    /// Why `def` can't be an initial predicate or a next-state relation, if it can't.
    pub(super) fn zero_arity_problem(&self, def: DefId) -> Option<EvalError> {
        let info = self.spec.def(def);
        let message = if info.depth > 0 {
            format!("{} is defined inside another definition.", info.name)
        } else if !info.params.is_empty() {
            format!("The operator {} requires {} arguments.", info.name, info.params.len())
        } else {
            return None;
        };
        Some(EvalError::at(&self.spec, info.module, info.span, message))
    }

    /// Reports the state the walk assigned, which must be complete unless it computes ENABLED.
    pub(super) fn complete(&self, run: &mut Run<'_>, action: Action) -> Result<()> {
        if run.computation == Computation::Enabled {
            run.is_stopped = true;
            return Ok(());
        }
        if !run.is_complete() {
            return Err(self.incomplete(run, action.name));
        }
        let state: State =
            run.assigned.iter().map(|value| value.clone().expect("complete")).collect();
        let found = run.found.as_mut().expect("an enumeration reports states");
        if !found(state)? {
            run.is_stopped = true;
        }
        Ok(())
    }

    fn incomplete(&self, run: &Run<'_>, action: Option<Symbol>) -> EvalError {
        let missing: Vec<VarId> = (0..run.assigned.len())
            .filter(|&index| run.assigned[index].is_none())
            .map(|index| VarId(index as u32))
            .collect();
        let names: Vec<&str> =
            missing.iter().map(|var| self.spec.variables[var.index()].name.as_str()).collect();
        let message = match run.computation {
            Computation::Init => "current state is not a legal state".to_owned(),
            _ => {
                // TLC names the action only when it splits the relation into several.
                let is_split = self.split_next(run.def).is_ok_and(|actions| actions.len() > 1);
                let subject = if is_split {
                    let name = action.unwrap_or(self.spec.def(run.def).name);
                    format!("action {name} of the next-state relation")
                } else {
                    "the next-state action".to_owned()
                };
                let (noun, verb) =
                    if names.len() > 1 { ("variables", "are") } else { ("variable", "is") };
                format!(
                    "Successor state is not completely specified by {subject}. The following {noun} {verb} not defined: {}.",
                    names.join(", ")
                )
            }
        };
        let info = self.spec.def(run.def);
        let mut error = EvalError::at(&self.spec, info.module, info.span, message);
        let state = run.assigned.iter().map(|value| value.as_ref().map(Value::to_string)).collect();
        let action = (run.computation == Computation::Next).then_some(action).flatten();
        error.incomplete = Some(Box::new(Incomplete { action, missing, state }));
        error
    }
}
