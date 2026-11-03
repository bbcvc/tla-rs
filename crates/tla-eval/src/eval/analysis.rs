//! Analyses of a resolved specification that the evaluator makes once, before it evaluates.

use std::collections::HashSet;

use tla_resolve::{Bound, DefBody, DefId, ExceptKey, Expr, ExprKind, OpRef, Scope, Spec};

/// Whether each definition is a function definition whose body refers to the function, itself
/// or through a definition inside it, by [`DefId`].
pub(crate) fn recursive_functions(spec: &Spec) -> Vec<bool> {
    (0..spec.defs.len())
        .map(|index| {
            let def = DefId(index as u32);
            match &spec.def(def).body {
                DefBody::Function { body, .. } => refers_to(spec, def, body),
                DefBody::Expr(_) => false,
            }
        })
        .collect()
}

fn refers_to(spec: &Spec, target: DefId, body: &Expr) -> bool {
    let depth = spec.def(target).depth;
    let mut visited = HashSet::new();
    let mut pending = vec![body];
    while let Some(expr) = pending.pop() {
        if let ExprKind::Call { def, .. } | ExprKind::OpArg(OpRef::Def { def, .. }) = &expr.kind {
            if *def == target {
                return true;
            }
            if spec.def(*def).depth > depth && visited.insert(*def) {
                match &spec.def(*def).body {
                    DefBody::Expr(body) => pending.push(body),
                    DefBody::Function { bounds, body } => {
                        pending.push(body);
                        pending.extend(bounds.iter().map(|bound| &bound.set));
                    }
                }
            }
        }
        for_each_child(expr, &mut |child| pending.push(child));
    }
    false
}

fn for_each_child<'e>(expr: &'e Expr, visit: &mut impl FnMut(&'e Expr)) {
    fn scope_args<'e>(scope: &'e Scope, visit: &mut impl FnMut(&'e Expr)) {
        if let Scope::Instance { parent, args } = scope {
            args.iter().for_each(&mut *visit);
            scope_args(parent, visit);
        }
    }
    fn bounds<'e>(bounds: &'e [Bound], visit: &mut impl FnMut(&'e Expr)) {
        bounds.iter().for_each(|bound| visit(&bound.set));
    }
    match &expr.kind {
        ExprKind::Bool(_)
        | ExprKind::Int(_)
        | ExprKind::Str(_)
        | ExprKind::Var(_)
        | ExprKind::Const(_)
        | ExprKind::Local(_) => {}
        ExprKind::Call { scope, args, .. } => {
            scope_args(scope, visit);
            args.iter().for_each(visit);
        }
        ExprKind::OpArg(OpRef::Def { scope, .. }) => scope_args(scope, visit),
        ExprKind::OpArg(_) => {}
        ExprKind::CallParam { args, .. }
        | ExprKind::CallConst { args, .. }
        | ExprKind::Builtin { args, .. }
        | ExprKind::And(args)
        | ExprKind::Or(args)
        | ExprKind::SetEnum(args)
        | ExprKind::Tuple(args)
        | ExprKind::Product(args) => args.iter().for_each(visit),
        ExprKind::If { cond, then, otherwise } => {
            visit(cond);
            visit(then);
            visit(otherwise);
        }
        ExprKind::Case { arms, other } => {
            for (guard, body) in arms {
                visit(guard);
                visit(body);
            }
            if let Some(other) = other {
                visit(other);
            }
        }
        ExprKind::Quant { bounds: quantified, body, .. }
        | ExprKind::SetMap { bounds: quantified, body }
        | ExprKind::Function { bounds: quantified, body } => {
            bounds(quantified, visit);
            visit(body);
        }
        ExprKind::UnboundedQuant { body, .. } => visit(body),
        ExprKind::Choose { set, body, .. } => {
            if let Some(set) = set {
                visit(set);
            }
            visit(body);
        }
        ExprKind::SetFilter { bound, pred } => {
            visit(&bound.set);
            visit(pred);
        }
        ExprKind::Record(fields) | ExprKind::RecordSet(fields) => {
            fields.iter().for_each(|(_, value)| visit(value));
        }
        ExprKind::FuncSet { domain: left, range: right }
        | ExprKind::BoxAction { action: left, sub: right }
        | ExprKind::AngleAction { action: left, sub: right }
        | ExprKind::Fairness { sub: left, action: right, .. } => {
            visit(left);
            visit(right);
        }
        ExprKind::FuncApp { func, args } => {
            visit(func);
            args.iter().for_each(visit);
        }
        ExprKind::Dot { record, .. } => visit(record),
        ExprKind::Except { base, updates } => {
            visit(base);
            for update in updates {
                for key in &update.path {
                    if let ExceptKey::Apply(args) = key {
                        args.iter().for_each(&mut *visit);
                    }
                }
                visit(&update.value);
            }
        }
    }
}
