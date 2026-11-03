//! Analyses of a resolved specification that the evaluator makes once, before it evaluates.

use std::collections::HashSet;

use tla_ast::Quantifier;
use tla_resolve::{
    Bound, Builtin, DefBody, DefId, ExceptKey, Expr, ExprKind, Level, OpRef, Scope, Spec,
};

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

/// The definition of `TLCEval` in TLC's standard module `TLC`, if the spec uses it.
pub(crate) fn tlc_eval(spec: &Spec) -> Option<DefId> {
    (0..spec.defs.len()).map(|index| DefId(index as u32)).find(|&id| {
        let def = spec.def(id);
        let module = &spec.modules[def.module.index()];
        module.is_standard && module.name.as_str() == "TLC" && def.name.as_str() == "TLCEval"
    })
}

/// The applications of `TLCEval` whose argument TLC's Java override normalizes, by the address
/// of each application. As tla-ts finds, TLC normalizes the value, and so fails on a set
/// enumeration it can't sort, only where it computes a constant once: for a constant argument,
/// in a module-level definition without parameters, outside every binder, and not in a module
/// that an `INSTANCE` substitutes into. Everywhere else `TLCEval(v)` is `v`.
pub(crate) fn normalizing_evaluations(spec: &Spec, tlc_eval: DefId) -> HashSet<usize> {
    let mut applications = HashSet::new();
    for def in &spec.defs {
        let DefBody::Expr(body) = &def.body else { continue };
        if def.depth > 0 || !def.params.is_empty() || def.is_instantiated {
            continue;
        }
        let mut pending = vec![body];
        while let Some(expr) = pending.pop() {
            if let ExprKind::Call { def, args, .. } = &expr.kind
                && *def == tlc_eval
                && args.iter().all(|arg| is_constant(spec, arg))
            {
                applications.insert(expr as *const Expr as usize);
            }
            for_each_unbound_child(expr, &mut |child| pending.push(child));
        }
    }
    applications
}

/// Whether an expression is constant, as SANY's levels decide it.
pub(super) fn is_constant(spec: &Spec, expr: &Expr) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        let is_constant = match &expr.kind {
            ExprKind::Var(_)
            | ExprKind::BoxAction { .. }
            | ExprKind::AngleAction { .. }
            | ExprKind::Fairness { .. } => false,
            ExprKind::Builtin { op, .. } => !matches!(
                op,
                Builtin::Prime
                    | Builtin::Unchanged
                    | Builtin::Enabled
                    | Builtin::Always
                    | Builtin::Eventually
                    | Builtin::LeadsTo
                    | Builtin::PlusArrow
                    | Builtin::Cdot
            ),
            ExprKind::UnboundedQuant { quantifier, .. } => {
                !matches!(quantifier, Quantifier::TemporalForall | Quantifier::TemporalExists)
            }
            ExprKind::Call { def, .. } | ExprKind::OpArg(OpRef::Def { def, .. }) => {
                spec.levels.get(def.index()).is_none_or(|levels| levels.level == Level::Constant)
            }
            _ => true,
        };
        if !is_constant {
            return false;
        }
        for_each_child(expr, &mut |child| pending.push(child));
    }
    true
}

/// The subexpressions of `expr` evaluated in its own scope, outside the bound variables of the
/// quantifiers, comprehensions, functions, and `EXCEPT`s it is made of.
fn for_each_unbound_child<'e>(expr: &'e Expr, visit: &mut impl FnMut(&'e Expr)) {
    match &expr.kind {
        ExprKind::Quant { bounds, .. }
        | ExprKind::SetMap { bounds, .. }
        | ExprKind::Function { bounds, .. } => bounds.iter().for_each(|bound| visit(&bound.set)),
        ExprKind::SetFilter { bound, .. } => visit(&bound.set),
        ExprKind::Choose { set, .. } => set.iter().for_each(|set| visit(set)),
        ExprKind::UnboundedQuant { .. } => {}
        ExprKind::Except { base, updates } => {
            visit(base);
            for update in updates {
                for key in &update.path {
                    if let ExceptKey::Apply(args) = key {
                        args.iter().for_each(&mut *visit);
                    }
                }
            }
        }
        _ => for_each_child(expr, visit),
    }
}

pub(super) fn for_each_child<'e>(expr: &'e Expr, visit: &mut impl FnMut(&'e Expr)) {
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

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use tla_resolve::RootName;

    use crate::{EvalError, Evaluator, State, Value};

    const INNER: &str =
        "---- MODULE Inner ----\nCONSTANT E(_)\nMixed == 1 \\in E({1, \"a\"})\n====\n";

    fn evaluator() -> Evaluator {
        let source = r#"
---- MODULE Evaluations ----
EXTENDS TLC
VARIABLE x
Direct == 1 \in TLCEval({1, "a"})
Bound == \E y \in {1} : y \in TLCEval({y, "a"})
Param(v) == 1 \in TLCEval(v)
Called == Param({1, "a"})
I == INSTANCE Inner WITH E <- TLCEval
Instantiated == I!Mixed
Stateful == 1 \in TLCEval({1, x})
====
"#;
        let spec = tla_resolve::resolve(source, &mut |name: &str| {
            (name == "Inner").then(|| INNER.to_owned())
        })
        .unwrap();
        Evaluator::new(Arc::new(spec), Vec::new())
    }

    fn eval(evaluator: &Evaluator, name: &str, state: Option<&State>) -> Result<Value, EvalError> {
        let Some(RootName::Def(def)) = evaluator.spec.lookup(name) else { panic!("{name}") };
        evaluator.eval_def(def, state)
    }

    /// tla-ts's NormalizationCases: TLCEval normalizes, and fails on a set enumeration it can't
    /// sort, only for a constant argument outside every binder and instance.
    #[test]
    fn normalizes_only_the_evaluations_tlc_computes_once() {
        let evaluator = evaluator();
        let error = eval(&evaluator, "Direct", None).unwrap_err().message;
        assert!(
            error.ends_with("Attempted to compare string \"a\" with non-string:\n1"),
            "{error}"
        );
        for name in ["Bound", "Called", "Instantiated"] {
            assert_eq!(eval(&evaluator, name, None).unwrap().to_string(), "TRUE", "{name}");
        }
        let state: State = vec![Value::str("a")].into();
        assert_eq!(eval(&evaluator, "Stateful", Some(&state)).unwrap().to_string(), "TRUE");
    }
}
