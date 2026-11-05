//! Whether the search may expand states in any order: what it evaluates has no effect another
//! order could show, as tla-ts `isImpure` decides before it searches with several workers. TLC's
//! operators that print, read the time or the model checker's state, keep registers, or choose
//! at random make a spec impure, unless only a constant definition TLC computes once when it
//! starts applies them.

use std::collections::{HashMap, HashSet};

use tla_tools_resolve::{DefBody, DefId, ExprKind, Level, OpRef, Spec};

use crate::level::{self, Levels, STATE_LEVEL_OPERATORS};
use crate::plan::Plan;

/// TLC's operators with effects besides those [`STATE_LEVEL_OPERATORS`] lists. A failing
/// `Assert` is an error, which the search with one worker reports, so it doesn't count.
const IMPURE_OPERATORS: &[(&str, &[&str])] =
    &[("TLC", &["Print", "PrintT", "JavaTime", "RandomElement"])];

/// Whether nothing the search evaluates for `plan` has an effect.
pub fn is_pure(spec: &Spec, plan: &Plan, overrides: &HashMap<DefId, DefId>) -> bool {
    let checks = [
        &plan.invariants,
        &plan.initial_predicates,
        &plan.action_properties,
        &plan.constraints,
        &plan.action_constraints,
    ];
    let mut pending: Vec<DefId> =
        plan.init.iter().copied().chain(plan.next).chain(plan.view).collect();
    pending.extend(checks.iter().flat_map(|checks| checks.iter().map(|check| check.def)));
    let levels = Levels::sany(STATE_LEVEL_OPERATORS);
    let mut visited: HashSet<DefId> = HashSet::new();
    while let Some(def) = pending.pop() {
        let def = *overrides.get(&def).unwrap_or(&def);
        if !visited.insert(def) {
            continue;
        }
        if is_impure_operator(spec, def) {
            return false;
        }
        let info = spec.def(def);
        // TLC computes a constant definition once, when it starts.
        let is_computed_once = info.depth == 0
            && info.params.is_empty()
            && levels.def_level(spec, def) == Level::Constant;
        if is_computed_once {
            continue;
        }
        let mut calls = |expr: &tla_tools_resolve::Expr| match &expr.kind {
            ExprKind::Call { def, .. } | ExprKind::OpArg(OpRef::Def { def, .. }) => {
                pending.push(*def)
            }
            _ => {}
        };
        match &info.body {
            DefBody::Expr(body) => level::visit(body, &mut calls),
            DefBody::Function { bounds, body } => {
                level::visit(body, &mut calls);
                bounds.iter().for_each(|bound| level::visit(&bound.set, &mut calls));
            }
        }
    }
    true
}

fn is_impure_operator(spec: &Spec, def: DefId) -> bool {
    let info = spec.def(def);
    let module = spec.modules[info.module.index()].name.as_str();
    info.depth == 0
        && STATE_LEVEL_OPERATORS
            .iter()
            .chain(IMPURE_OPERATORS)
            .any(|(name, operators)| *name == module && operators.contains(&info.name.as_str()))
}
