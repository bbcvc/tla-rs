//! The conjuncts that assign variables: `x' = e`, `x' \in S`, `x' \subseteq S`, and `UNCHANGED`,
//! or `x = e` and `x \in S` in an initial predicate.

use std::sync::Arc;

use tla_resolve::{Builtin, DefBody, Expr, ExprKind};
use tla_value::{LazySet, Value};

use super::run::{Computation, Run, env};
use super::{Action, Rest, Site};
use crate::env::{Enabled, Slot};
use crate::eval::At;
use crate::eval::builtin::is_overridden;
use crate::{Evaluator, Result};

/// How deep the walk follows definitions and arguments to find the variable a conjunct assigns.
const MAXIMUM_TARGET_DEPTH: usize = 64;

impl Evaluator {
    /// The variable `target` assigns: `x'` in an action, or `x` in an initial predicate, written
    /// directly, through a definition without parameters, or through an argument.
    pub(super) fn target(
        &self,
        target: &Expr,
        site: &Site,
        run: &Run<'_>,
    ) -> Result<Option<usize>> {
        let is_primed = run.computation != Computation::Init;
        self.target_at(target, site, run, is_primed, 0)
    }

    fn target_at(
        &self,
        target: &Expr,
        site: &Site,
        run: &Run<'_>,
        is_primed: bool,
        depth: usize,
    ) -> Result<Option<usize>> {
        if depth > MAXIMUM_TARGET_DEPTH {
            return Ok(None);
        }
        match &target.kind {
            ExprKind::Builtin { op: Builtin::Prime, args } if is_primed => {
                self.target_at(&args[0], site, run, false, depth + 1)
            }
            ExprKind::Var(var) if !is_primed => Ok(Some(self.slot(var.index(), target, site))),
            ExprKind::Local(local) => match &site.frame.up(local.hops).slots[local.slot] {
                Slot::Thunk(thunk) if Arc::ptr_eq(thunk.expr.spec(), &self.spec) => {
                    let origin = Site::of(&thunk.captured);
                    self.target_at(thunk.expr.get(), &origin, run, is_primed, depth + 1)
                }
                _ => Ok(None),
            },
            ExprKind::Call { def, scope, args } if args.is_empty() => {
                let Some(target) = self.walked(*def, 0) else { return Ok(None) };
                let DefBody::Expr(body) = &self.spec.def(target).body else { return Ok(None) };
                let callee = self.entered(*def, target, scope, args, site, run)?;
                self.target_at(body, &callee, run, is_primed, depth + 1)
            }
            _ => Ok(None),
        }
    }

    /// The slot of the state being assigned that the variable `var`, written `expr`, assigns:
    /// its own, or in the operand of an ENABLED of an instantiated module, the one TLC binds the
    /// module's variable to.
    fn slot(&self, var: usize, expr: &Expr, site: &Site) -> usize {
        if site.enabled == Enabled::Outside {
            return var;
        }
        let address = expr as *const Expr as usize;
        self.instance_enabled.variables.get(&address).copied().unwrap_or(var)
    }

    /// `x' = e`, `x' \in S`, or `x' \subseteq S` for the variable `var`: assigns `var` if the
    /// walk hasn't yet, for each element of `S` as TLC's `Enumerator` streams it, and tests it
    /// otherwise. A lazy union TLC hasn't cached streams each set it combines, so an element two
    /// of them share is assigned once for each.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn assign(
        &self,
        var: usize,
        op: Builtin,
        value: &Expr,
        expr: &Expr,
        site: &Site,
        run: &mut Run<'_>,
        action: Action,
        rest: &Rest<'_>,
    ) -> Result<()> {
        if run.assigned[var].is_some() {
            return self.guard(expr, site, run, action, rest);
        }
        let value = self.evaluate_in(value, site, run)?;
        if op == Builtin::Eq {
            return run.with_assigned(var, value, |run| self.resume(run, action, rest));
        }
        let set = if op == Builtin::SubsetEq { Value::lazy(LazySet::Subset(value)) } else { value };
        let env = env(site, run);
        if !set.is_set() || is_overridden(&set) {
            let message = match run.computation {
                Computation::Enabled => "The right side of \\IN is not enumerable.".to_owned(),
                computation => format!(
                    "In computing {}, the right side of \\IN is not enumerable.",
                    computation.name()
                ),
            };
            let message = format!("{message}\n{}", self.range(&env, expr));
            return Err(self.error(&env, expr, message));
        }
        let elements = set.streamed_elements().at(self, &env, expr)?;
        drop(env);
        for element in elements.iter() {
            run.with_assigned(var, element.clone(), |run| self.resume(run, action, rest))?;
            if run.is_stopped {
                break;
            }
        }
        Ok(())
    }

    /// `UNCHANGED sub` as a conjunct of an action: assigns each variable `sub` keeps its current
    /// value if the walk hasn't yet, and tests it otherwise.
    pub(super) fn unchanged_action(
        &self,
        sub: &Expr,
        expr: &Expr,
        site: &Site,
        run: &mut Run<'_>,
        action: Action,
        rest: &Rest<'_>,
    ) -> Result<()> {
        if run.computation == Computation::Init {
            let env = env(site, run);
            let message = format!(
                "UNCHANGED appears in an initial predicate at {}",
                self.location(&env, expr)
            );
            return Err(self.error(&env, expr, message));
        }
        self.keep(sub, site, run, action, rest, 0)
    }

    /// Keeps one part of the subscript of `UNCHANGED`: a variable, a tuple of parts, or a
    /// definition without parameters or an argument that stands for one, and tests any other
    /// expression.
    pub(super) fn keep(
        &self,
        sub: &Expr,
        site: &Site,
        run: &mut Run<'_>,
        action: Action,
        rest: &Rest<'_>,
        depth: usize,
    ) -> Result<()> {
        match &sub.kind {
            _ if depth > MAXIMUM_TARGET_DEPTH => {}
            ExprKind::Tuple(items) => {
                let Some((first, others)) = items.split_first() else {
                    return self.resume(run, action, rest);
                };
                let rest = Rest::Kept { items: others, site, rest };
                return self.keep(first, site, run, action, &rest, depth + 1);
            }
            ExprKind::Var(var) => {
                let current =
                    run.current.expect("an action has a current state")[var.index()].clone();
                let var = self.slot(var.index(), sub, site);
                return match &run.assigned[var] {
                    None => run.with_assigned(var, current, |run| self.resume(run, action, rest)),
                    Some(assigned) => {
                        let is_kept = assigned.equals(&current).at(self, &env(site, run), sub)?;
                        if is_kept { self.resume(run, action, rest) } else { Ok(()) }
                    }
                };
            }
            ExprKind::Local(local) => {
                if let Slot::Thunk(thunk) = &site.frame.up(local.hops).slots[local.slot]
                    && Arc::ptr_eq(thunk.expr.spec(), &self.spec)
                {
                    let thunk = thunk.clone();
                    let origin = Site::of(&thunk.captured);
                    return self.keep(thunk.expr.get(), &origin, run, action, rest, depth + 1);
                }
            }
            ExprKind::Call { def, scope, args }
                if args.is_empty()
                    && let Some(target) = self.walked(*def, 0) =>
            {
                let DefBody::Expr(body) = &self.spec.def(target).body else { unreachable!() };
                let callee = self.entered(*def, target, scope, args, site, run)?;
                return self.keep(body, &callee, run, action, rest, depth + 1);
            }
            _ => {}
        }
        let is_kept = self.unchanged(sub, sub, &mut env(site, run))?;
        if is_kept { self.resume(run, action, rest) } else { Ok(()) }
    }
}
