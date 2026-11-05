//! Successor generation: the states an initial predicate or an action allows, enumerated as TLC's
//! `getInitStates` and `getNextStates` enumerate them, ported from tla-ts's `successors.ts`.
//!
//! The walk follows the structure of the predicate. A conjunction walks its conjuncts left to
//! right, a disjunction or `\E` walks each branch in turn, and `x' = e`, `x' \in S`, and
//! `UNCHANGED x` assign a variable the first time the walk meets it and test it after. Any other
//! conjunct is a guard. What remains to walk after a conjunct is a continuation, [`Rest`], so a
//! branch assigns variables in place and undoes them when it returns, instead of copying the
//! state for each branch.

mod apply;
mod assign;
mod run;
mod split;

use std::sync::Arc;

use tla_tools_ast::Quantifier;
use tla_tools_resolve::{Builtin, DefBody, DefId, Expr, ExprKind, ModuleId, Scope};
use tla_tools_value::{Symbol, Value};

pub(crate) use self::run::Computation;
use self::run::{Run, env};
pub use self::split::NextAction;
use super::bound::{Variable, bind_frame};
use super::{STACK_OVERFLOW, describe, is_stack_low};
use crate::env::{Captured, Enabled, Frame, Slot};
use crate::native::OperatorKind;
use crate::{ConstBinding, EvalError, Evaluator, Result};

/// Where an action expression is: the frame it reads its parameters and bound variables from,
/// and the module whose text holds it.
#[derive(Clone)]
pub(crate) struct Site {
    pub frame: Arc<Frame>,
    pub module: ModuleId,
    /// Whether the expression is in the operand of an ENABLED of an instantiated module.
    pub enabled: Enabled,
}

/// The action TLC names a successor after: the last definition the walk called outside a
/// conjunction. A conjunct keeps the name of the conjunction.
#[derive(Clone, Copy, Default)]
pub(super) struct Action {
    pub name: Option<Symbol>,
    is_fixed: bool,
}

impl Site {
    /// Where an argument or a lazy function was written, which it keeps.
    pub(super) fn of(captured: &Captured) -> Self {
        Site { frame: captured.frame.clone(), module: captured.module, enabled: captured.enabled }
    }
}

impl Action {
    fn called(self, name: Symbol) -> Self {
        if self.is_fixed { self } else { Self { name: Some(name), is_fixed: false } }
    }

    fn fixed(self) -> Self {
        Self { is_fixed: true, ..self }
    }
}

/// What the walk does once the predicate it walks holds: the continuation of a conjunct.
pub(super) enum Rest<'a> {
    /// The state is complete: report it.
    Done,
    /// Walk `conjuncts` in `site`, then `rest`.
    Conjuncts { conjuncts: &'a [Expr], site: &'a Site, rest: &'a Rest<'a> },
    /// Walk the bodies of the zero-arity definitions `defs`, each in its own frame, then `rest`.
    Defs { defs: &'a [DefId], rest: &'a Rest<'a> },
    /// Walk `body` in each of `sites`, as `\A` does in an action, then `rest`.
    Each { body: &'a Expr, sites: &'a [Site], is_first: bool, rest: &'a Rest<'a> },
    /// Continue with `rest` only if `sub` changed, as `<<A>>_sub` requires after `A`.
    Changed { sub: &'a Expr, site: &'a Site, rest: &'a Rest<'a> },
    /// Keep the variables of the parts `items` of the subscript of an `UNCHANGED`, then `rest`.
    Kept { items: &'a [Expr], site: &'a Site, rest: &'a Rest<'a> },
}

impl Evaluator {
    /// Continues the walk with `rest`.
    fn resume(&self, run: &mut Run<'_>, action: Action, rest: &Rest<'_>) -> Result<()> {
        if run.is_stopped {
            return Ok(());
        }
        match *rest {
            Rest::Done => self.complete(run, action),
            Rest::Conjuncts { conjuncts, site, rest } => {
                self.conjoin(conjuncts, false, site, run, action, rest)
            }
            Rest::Defs { defs, rest } => match defs.split_first() {
                None => self.resume(run, action, rest),
                Some((&first, others)) => {
                    self.enter_definition(first, run, action, &Rest::Defs { defs: others, rest })
                }
            },
            Rest::Each { body, sites, is_first, rest } => {
                let Some((first, others)) = sites.split_first() else {
                    return self.resume(run, action, rest);
                };
                if !is_first && run.computation == Computation::Init && run.is_complete() {
                    for site in sites {
                        if !self.holds(body, site, run, true)? {
                            return Ok(());
                        }
                    }
                    return self.resume(run, action, rest);
                }
                let rest = Rest::Each { body, sites: others, is_first: false, rest };
                self.act(body, first, run, action.fixed(), &rest)
            }
            Rest::Kept { items, site, rest } => match items.split_first() {
                None => self.resume(run, action, rest),
                Some((first, others)) => self.keep(
                    first,
                    site,
                    run,
                    action,
                    &Rest::Kept { items: others, site, rest },
                    0,
                ),
            },
            Rest::Changed { sub, site, rest } => {
                let mut env = env(site, run);
                if self.unchanged(sub, sub, &mut env)? {
                    return Ok(());
                }
                self.resume(run, action, rest)
            }
        }
    }

    /// Walks the conjuncts of `site` in turn, then `rest`. `is_first` tells the first conjunct
    /// of a conjunction from the conjuncts left after one. A conjunct that is a plain guard is
    /// tested in place, rather than walked with what follows it as its continuation, which
    /// keeps the stack of a long conjunction of guards flat.
    fn conjoin(
        &self,
        mut conjuncts: &[Expr],
        mut is_first: bool,
        site: &Site,
        run: &mut Run<'_>,
        action: Action,
        rest: &Rest<'_>,
    ) -> Result<()> {
        loop {
            let Some((first, others)) = conjuncts.split_first() else {
                return self.resume(run, action, rest);
            };
            // Once every variable has a value, TLC evaluates the conjuncts left as predicates,
            // so a disjunction among them yields one state rather than one for each disjunct
            // that holds. Its getNextStates does so only with warnings on.
            if !is_first && run.is_shortcut && run.is_complete() {
                for conjunct in conjuncts {
                    if !self.holds(conjunct, site, run, false)? {
                        return Ok(());
                    }
                }
                return self.resume(run, action, rest);
            }
            if !is_walked(first) {
                if !self.holds(first, site, run, true)? {
                    return Ok(());
                }
                (conjuncts, is_first) = (others, false);
                continue;
            }
            let rest = Rest::Conjuncts { conjuncts: others, site, rest };
            return self.act(first, site, run, action.fixed(), &rest);
        }
    }

    /// Walks the predicate `expr` of `site`, continuing with `rest` for each way it holds.
    fn act(
        &self,
        expr: &Expr,
        site: &Site,
        run: &mut Run<'_>,
        action: Action,
        rest: &Rest<'_>,
    ) -> Result<()> {
        if run.is_stopped {
            return Ok(());
        }
        match &expr.kind {
            ExprKind::And(items) | ExprKind::Builtin { op: Builtin::And, args: items } => {
                self.conjoin(items, true, site, run, action, rest)
            }
            ExprKind::Or(items) | ExprKind::Builtin { op: Builtin::Or, args: items } => {
                for item in items {
                    self.act(item, site, run, action, rest)?;
                    if run.is_stopped {
                        break;
                    }
                }
                Ok(())
            }
            ExprKind::If { cond, then, otherwise } => {
                let branch = match self.evaluate_in(cond, site, run)? {
                    Value::Bool(true) => then,
                    Value::Bool(false) => otherwise,
                    value => return Err(self.if_error(expr, &value, site, run)),
                };
                self.act(branch, site, run, action, rest)
            }
            ExprKind::Case { arms, other } => {
                for (guard, body) in arms {
                    match self.evaluate_in(guard, site, run)? {
                        Value::Bool(true) => return self.act(body, site, run, action, rest),
                        Value::Bool(false) => {}
                        value => {
                            let env = env(site, run);
                            let space =
                                if run.computation == Computation::Enabled { "" } else { " " };
                            let message = format!(
                                "In computing {}, a non-boolean expression{space}({}) was used as a guard condition of a CASE.\n{}",
                                run.computation.name(),
                                describe(&value),
                                self.node(&env, body)
                            );
                            return Err(self.error(&env, guard, message));
                        }
                    }
                }
                match other {
                    Some(other) => self.act(other, site, run, action, rest),
                    None => {
                        let env = env(site, run);
                        let message = format!(
                            "In computing {}, TLC encountered a CASE with no conditions true.\n{}",
                            run.computation.name(),
                            self.range(&env, expr)
                        );
                        Err(self.error(&env, expr, message))
                    }
                }
            }
            ExprKind::Quant { quantifier: Quantifier::Exists, bounds, body } => {
                let variables = self.variables(bounds, &mut env(site, run))?;
                self.for_each_site(&variables, site, run, |evaluator, run, bound| {
                    evaluator.act(body, bound, run, action, rest)
                })
            }
            ExprKind::Quant { quantifier: Quantifier::Forall, bounds, body } => {
                let variables = self.variables(bounds, &mut env(site, run))?;
                let mut sites = Vec::new();
                self.for_each_site(&variables, site, run, |_, _, bound| {
                    sites.push(bound.clone());
                    Ok(())
                })?;
                // TLC walks the first binding, then the others from the last.
                if sites.len() > 1 {
                    sites[1..].reverse();
                }
                self.resume(run, action, &Rest::Each { body, sites: &sites, is_first: true, rest })
            }
            ExprKind::Builtin {
                op: op @ (Builtin::Eq | Builtin::In | Builtin::SubsetEq),
                args,
            } => match self.target(&args[0], site, run)? {
                Some(var) => self.assign(var, *op, &args[1], expr, site, run, action, rest),
                None => self.guard(expr, site, run, action, rest),
            },
            ExprKind::Builtin { op: Builtin::Unchanged, args } => {
                self.unchanged_action(&args[0], expr, site, run, action, rest)
            }
            ExprKind::Builtin { op: Builtin::Implies, args } => {
                match self.evaluate_in(&args[0], site, run)? {
                    Value::Bool(false) => self.resume(run, action, rest),
                    Value::Bool(true) => self.act(&args[1], site, run, action, rest),
                    value => {
                        let env = env(site, run);
                        let message = format!(
                            "Expected the left side of => at {} to be a boolean but found {value}",
                            self.location(&env, &args[0])
                        );
                        Err(self.error(&env, &args[0], message))
                    }
                }
            }
            ExprKind::BoxAction { action: inner, sub } => {
                self.act(inner, site, run, action, rest)?;
                if run.is_stopped {
                    return Ok(());
                }
                self.unchanged_action(sub, expr, site, run, action, rest)
            }
            ExprKind::AngleAction { action: inner, sub } => {
                self.act(inner, site, run, action, &Rest::Changed { sub, site, rest })
            }
            ExprKind::Call { def, scope, args } => {
                self.act_call(*def, scope, args, expr, site, run, action, rest)
            }
            ExprKind::CallConst { id, args } => match self.constants.get(id.index()) {
                Some(ConstBinding::Def(def)) => {
                    self.act_call(*def, &Scope::Global, args, expr, site, run, action, rest)
                }
                _ => self.guard(expr, site, run, action, rest),
            },
            ExprKind::CallParam { param, args } => {
                let operator = match &site.frame.up(param.hops).slots[param.slot] {
                    Slot::Op(op) => op.clone(),
                    _ => return self.guard(expr, site, run, action, rest),
                };
                let OperatorKind::Def { def, parent, enabled } = &operator.0 else {
                    if let (OperatorKind::Builtin(Builtin::Unchanged), [arg]) =
                        (&operator.0, &args[..])
                    {
                        return self.unchanged_action(arg, expr, site, run, action, rest);
                    }
                    return self.guard(expr, site, run, action, rest);
                };
                let Some(target) = self.walked(*def, args.len()) else {
                    return self.guard(expr, site, run, action, rest);
                };
                let parent = if target == *def { parent.clone() } else { None };
                let mut callee = self.callee(target, parent, args, site, run)?;
                // The operator keeps the mode of where it was passed.
                callee.enabled = *enabled;
                let info = self.spec.def(target);
                let DefBody::Expr(body) = &info.body else { unreachable!("a walked definition") };
                self.act(body, &callee, run, action.called(info.name), rest)
            }
            ExprKind::FuncApp { func, args } => {
                self.act_application(func, args, expr, site, run, action, rest)
            }
            ExprKind::Local(local) => {
                // An argument that is an action, as `A` in `Op(A) == A /\ ...`, is walked where
                // the call wrote it.
                let thunk = match &site.frame.up(local.hops).slots[local.slot] {
                    Slot::Thunk(thunk) if Arc::ptr_eq(thunk.expr.spec(), &self.spec) => {
                        thunk.clone()
                    }
                    _ => return self.guard(expr, site, run, action, rest),
                };
                let origin = Site::of(&thunk.captured);
                self.act(thunk.expr.get(), &origin, run, action, rest)
            }
            _ => self.guard(expr, site, run, action, rest),
        }
    }

    /// The definition whose body the walk enters for a call of `def` with `arity` arguments,
    /// as TLC looks it up: the definition the configuration replaces it with, `Op <- Other`,
    /// through any further replacement, or `def` itself. `None` where the walk evaluates the
    /// call instead: a definition a native or a value replaces, or a function definition.
    fn walked(&self, def: DefId, arity: usize) -> Option<DefId> {
        let mut target = def;
        for _ in 0..self.spec.defs.len() {
            match &self.overrides[target.index()] {
                Some(ConstBinding::Def(other)) => target = *other,
                Some(_) => return None,
                None => break,
            }
        }
        let info = self.spec.def(target);
        let is_walked = self.overrides[target.index()].is_none()
            && self.natives[target.index()].is_none()
            && self.tlc_eval != Some(target)
            && matches!(info.body, DefBody::Expr(_))
            && info.params.len() == arity
            // A replacement is a definition of the root module, outside every frame.
            && (target == def || info.depth == 0);
        is_walked.then_some(target)
    }

    /// The site of the body of `target`, which the walk enters for a call of `def` in `scope`
    /// with `args` of `site`. A definition the configuration replaces `def` with is at the top
    /// level, outside the call's scope.
    #[allow(clippy::too_many_arguments)]
    fn entered(
        &self,
        def: DefId,
        target: DefId,
        scope: &Scope,
        args: &[Expr],
        site: &Site,
        run: &Run<'_>,
    ) -> Result<Site> {
        let parent = if target == def { self.scope_frame(scope, &env(site, run))? } else { None };
        self.callee(target, parent, args, site, run)
    }

    #[allow(clippy::too_many_arguments)]
    fn act_call(
        &self,
        def: DefId,
        scope: &Scope,
        args: &[Expr],
        expr: &Expr,
        site: &Site,
        run: &mut Run<'_>,
        action: Action,
        rest: &Rest<'_>,
    ) -> Result<()> {
        let Some(target) = self.walked(def, args.len()) else {
            return self.guard(expr, site, run, action, rest);
        };
        if is_stack_low() {
            return Err(self.error(&env(site, run), expr, STACK_OVERFLOW));
        }
        let callee = self.entered(def, target, scope, args, site, run)?;
        let info = self.spec.def(target);
        let DefBody::Expr(body) = &info.body else { unreachable!("a walked definition") };
        // TLC names the action as SANY names the operator: I!Op through the instance I.
        let name = match action.is_fixed {
            true => info.name,
            false => {
                let qualified = self.spec.qualified_names.get(&(site.module, expr.span));
                qualified.copied().unwrap_or(info.name)
            }
        };
        self.act(body, &callee, run, action.called(name), rest)
    }

    /// The site of the body of `def` called with `args` of `site`, in a frame whose parent is
    /// `parent`.
    fn callee(
        &self,
        def: DefId,
        parent: Option<Arc<Frame>>,
        args: &[Expr],
        site: &Site,
        run: &Run<'_>,
    ) -> Result<Site> {
        let info = self.spec.def(def);
        let env = env(site, run);
        let slots = args.iter().map(|arg| self.arg_slot(arg, &env)).collect::<Result<Vec<_>>>()?;
        Ok(Site {
            frame: Arc::new(Frame::new(slots, info.frame_size, parent)),
            module: info.module,
            enabled: site.enabled,
        })
    }

    /// Binds the variables to each combination of their elements in a copy of the frame of
    /// `site`, the first variable varying fastest, and visits each until the run stops.
    fn for_each_site(
        &self,
        variables: &[Variable<'_>],
        site: &Site,
        run: &mut Run<'_>,
        mut visit: impl FnMut(&Self, &mut Run<'_>, &Site) -> Result<()>,
    ) -> Result<()> {
        self.for_each_bound_site(variables, site, |bound| {
            if run.is_stopped {
                return Ok(false);
            }
            visit(self, run, bound)?;
            Ok(true)
        })
    }

    /// Binds the variables to each combination of their elements in a copy of the frame of
    /// `site`, the first variable varying fastest, and visits each until `visit` returns false.
    fn for_each_bound_site(
        &self,
        variables: &[Variable<'_>],
        site: &Site,
        mut visit: impl FnMut(&Site) -> Result<bool>,
    ) -> Result<()> {
        if variables.iter().any(|variable| variable.elements.is_empty()) {
            return Ok(());
        }
        let mut bound = site.clone();
        let bind = |bound: &mut Site, variable: &Variable<'_>, index: usize| {
            bind_frame(variable.binder, variable.elements.get(index), &mut bound.frame)
                .map_err(|error| EvalError::at(&self.spec, site.module, variable.set.span, error.0))
        };
        let mut indexes = vec![0; variables.len()];
        for variable in variables.iter().rev() {
            bind(&mut bound, variable, 0)?;
        }
        loop {
            if !visit(&bound)? {
                return Ok(());
            }
            let mut position = 0;
            loop {
                let Some(variable) = variables.get(position) else { return Ok(()) };
                indexes[position] += 1;
                if indexes[position] < variable.elements.len() {
                    bind(&mut bound, variable, indexes[position])?;
                    break;
                }
                indexes[position] = 0;
                bind(&mut bound, variable, 0)?;
                position += 1;
            }
        }
    }

    /// Continues with `rest` if the guard `expr` holds.
    fn guard(
        &self,
        expr: &Expr,
        site: &Site,
        run: &mut Run<'_>,
        action: Action,
        rest: &Rest<'_>,
    ) -> Result<()> {
        if self.holds(expr, site, run, true)? { self.resume(run, action, rest) } else { Ok(()) }
    }

    /// Whether `expr` holds. `is_walked` tells a conjunct the walk reached from one it evaluates
    /// because every variable already has a value, which TLC words differently when it isn't a
    /// boolean.
    fn holds(&self, expr: &Expr, site: &Site, run: &Run<'_>, is_walked: bool) -> Result<bool> {
        let mut env = env(site, run);
        match self.eval(expr, &mut env)? {
            Value::Bool(value) => Ok(value),
            value => {
                let node = self.node(&env, expr);
                let is_literal = matches!(expr.kind, ExprKind::Int(_) | ExprKind::Str(_));
                let message = match run.computation {
                    Computation::Enabled if is_walked && is_literal => {
                        format!("Attempted to compute ENABLED on a non-boolean expression.\n{node}")
                    }
                    computation if is_walked && is_literal => {
                        let relation =
                            if computation == Computation::Init { "init" } else { "next" };
                        format!(
                            "The {relation} state relation is not a boolean expression.\n{node}"
                        )
                    }
                    computation => format!(
                        "In computing {}, TLC expected a boolean expression,\nbut instead found {value}.\n{node}",
                        computation.name()
                    ),
                };
                Err(self.error(&env, expr, message))
            }
        }
    }

    fn evaluate_in(&self, expr: &Expr, site: &Site, run: &Run<'_>) -> Result<Value> {
        self.eval(expr, &mut env(site, run))
    }

    fn if_error(&self, expr: &Expr, value: &Value, site: &Site, run: &Run<'_>) -> EvalError {
        let env = env(site, run);
        let (kind, range) = (describe(value), self.range(&env, expr));
        let message = match run.computation {
            Computation::Enabled => format!(
                "In computing ENABLED, a non-boolean expression({kind}) was used as the guard condition of an IF.\n{range}"
            ),
            computation => {
                let separator = if computation == Computation::Init { "\n" } else { "" };
                format!(
                    "In computing {}, a non-boolean expression ({kind}) was used as the condition of an IF.{separator}{range}",
                    computation.name()
                )
            }
        };
        self.error(&env, expr, message)
    }
}

/// Whether [`Evaluator::act`] walks `expr` rather than test it as a guard: a kind of expression
/// it may assign variables through.
fn is_walked(expr: &Expr) -> bool {
    matches!(
        expr.kind,
        ExprKind::And(_)
            | ExprKind::Or(_)
            | ExprKind::If { .. }
            | ExprKind::Case { .. }
            | ExprKind::Quant { quantifier: Quantifier::Exists | Quantifier::Forall, .. }
            | ExprKind::Builtin {
                op: Builtin::And
                    | Builtin::Or
                    | Builtin::Eq
                    | Builtin::In
                    | Builtin::SubsetEq
                    | Builtin::Unchanged
                    | Builtin::Implies,
                ..
            }
            | ExprKind::BoxAction { .. }
            | ExprKind::AngleAction { .. }
            | ExprKind::Call { .. }
            | ExprKind::CallConst { .. }
            | ExprKind::CallParam { .. }
            | ExprKind::FuncApp { .. }
            | ExprKind::Local(_)
    )
}

#[cfg(test)]
mod tests;
