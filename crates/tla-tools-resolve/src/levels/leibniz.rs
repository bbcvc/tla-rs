//! The parameters an expression uses where the Leibniz rule fails, which SANY forbids an
//! operator substituted for a constant operator to have (tla-ts `getNonLeibnizNames`).

use std::collections::BTreeSet;

use tla_tools_ast::Quantifier;

use super::analyzer::{Analyzer, Body};
use super::data::Param;
use crate::ir::{Bound, Builtin, ExceptKey, Expr, ExprKind};

impl Analyzer<'_> {
    /// Adds to `names` the parameters `expr` uses where substituting equal values for them could
    /// give unequal results: under a prime, `ENABLED`, `UNCHANGED`, or a temporal operator.
    /// Following tla-ts, and SANY, it doesn't look into `LET`s or operator arguments.
    pub(super) fn leibniz(
        &mut self,
        body: &Body,
        expr: &Expr,
        is_non_leibniz: bool,
        names: &mut BTreeSet<Param>,
    ) {
        if body.is_let_body(expr.span) {
            return;
        }
        let flag = is_non_leibniz;
        match &expr.kind {
            ExprKind::Bool(_)
            | ExprKind::Int(_)
            | ExprKind::Str(_)
            | ExprKind::Var(_)
            | ExprKind::Const(_)
            | ExprKind::OpArg(_) => {}
            ExprKind::Local(local) => {
                if flag {
                    names.insert(body.param(*local));
                }
            }
            ExprKind::Call { def, scope, args } => {
                let (operator, instance_args) = self.callee(*def, scope);
                let all = instance_args.into_iter().chain(args);
                for (index, arg) in all.enumerate() {
                    let is_arg_non_leibniz = flag || operator.non_leibniz.contains(&index);
                    self.leibniz(body, arg, is_arg_non_leibniz, names);
                }
            }
            ExprKind::CallParam { param, args } => {
                if flag {
                    names.insert(body.param(*param));
                }
                self.leibniz_all(body, args, flag, names);
            }
            ExprKind::CallConst { args, .. } => self.leibniz_all(body, args, flag, names),
            ExprKind::Builtin { op, args } => {
                let is_operator_non_leibniz = matches!(
                    op,
                    Builtin::Prime
                        | Builtin::Unchanged
                        | Builtin::Enabled
                        | Builtin::Always
                        | Builtin::Eventually
                        | Builtin::LeadsTo
                        | Builtin::PlusArrow
                        | Builtin::Cdot
                );
                self.leibniz_all(body, args, flag || is_operator_non_leibniz, names);
            }
            ExprKind::BoxAction { action, sub } | ExprKind::AngleAction { action, sub } => {
                self.leibniz_all(body, &[&**action, &**sub], true, names);
            }
            ExprKind::Fairness { sub, action, .. } => {
                self.leibniz_all(body, &[&**sub, &**action], true, names);
            }
            ExprKind::UnboundedQuant { quantifier, body: predicate, .. } => {
                let is_temporal =
                    matches!(quantifier, Quantifier::TemporalForall | Quantifier::TemporalExists);
                self.leibniz(body, predicate, flag || is_temporal, names);
            }
            _ => self.leibniz_all(body, &children(expr), flag, names),
        }
    }

    fn leibniz_all<E: std::borrow::Borrow<Expr>>(
        &mut self,
        body: &Body,
        exprs: &[E],
        is_non_leibniz: bool,
        names: &mut BTreeSet<Param>,
    ) {
        for expr in exprs {
            self.leibniz(body, expr.borrow(), is_non_leibniz, names);
        }
    }
}

/// The sets of `bounds`, then `last`.
fn with_sets<'e>(bounds: &'e [Bound], last: &'e Expr) -> Vec<&'e Expr> {
    bounds.iter().map(|bound| &bound.set).chain([last]).collect()
}

/// The subexpressions of an expression whose operator is Leibniz in all of them.
fn children(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::And(items)
        | ExprKind::Or(items)
        | ExprKind::SetEnum(items)
        | ExprKind::Tuple(items)
        | ExprKind::Product(items) => items.iter().collect(),
        ExprKind::If { cond, then, otherwise } => vec![&**cond, &**then, &**otherwise],
        ExprKind::Case { arms, other } => {
            let mut children: Vec<&Expr> =
                arms.iter().flat_map(|(guard, arm)| [guard, arm]).collect();
            children.extend(other.as_deref());
            children
        }
        ExprKind::Quant { bounds, body, .. }
        | ExprKind::SetMap { bounds, body }
        | ExprKind::Function { bounds, body } => with_sets(bounds, body),
        ExprKind::Choose { set, body, .. } => set.as_deref().into_iter().chain([&**body]).collect(),
        ExprKind::SetFilter { bound, pred } => vec![&bound.set, &**pred],
        ExprKind::Record(fields) | ExprKind::RecordSet(fields) => {
            fields.iter().map(|(_, value)| value).collect()
        }
        ExprKind::FuncSet { domain, range } => vec![&**domain, &**range],
        ExprKind::FuncApp { func, args } => [&**func].into_iter().chain(args).collect(),
        ExprKind::Dot { record, .. } => vec![&**record],
        ExprKind::Except { base, updates } => {
            let mut children = vec![&**base];
            for update in updates {
                for key in &update.path {
                    if let ExceptKey::Apply(args) = key {
                        children.extend(args);
                    }
                }
                children.push(&update.value);
            }
            children
        }
        _ => Vec::new(),
    }
}
