//! Functions: construction, function definitions, application, field selection, and `EXCEPT`.

use std::collections::HashSet;
use std::sync::Arc;

use tla_resolve::{
    Bound, DefBody, DefId, ExceptKey, ExceptUpdate, Expr, ExprKind, OpRef, Scope, Spec,
};
use tla_value::{Error, Key, LazyFunc, LazySet, Symbol, Value};

use super::bound::{Binder, Variable, bind, binders, tuple_items};
use super::{At, describe};
use crate::env::{Env, SpecRef};
use crate::{EvalError, Evaluator, Result};

impl Evaluator {
    /// `[x \in S, ... |-> body]`. TLC enumerates the function when it can enumerate its domain,
    /// unless `is_lazy` or the function is being applied, and otherwise evaluates the body only
    /// at the arguments it is applied to.
    #[inline(never)]
    pub(super) fn function(
        &self,
        bounds: &[Bound],
        body: &Expr,
        expr: &Expr,
        env: &mut Env<'_>,
        is_lazy: bool,
    ) -> Result<Value> {
        let sets =
            bounds.iter().map(|bound| self.eval(&bound.set, env)).collect::<Result<Vec<_>>>()?;
        let mut factors = Vec::new();
        for (bound, set) in bounds.iter().zip(&sets) {
            factors.extend(binders(&bound.pattern).map(|_| set.clone()));
        }
        let domain = match <[Value; 1]>::try_from(factors) {
            Ok([set]) => set,
            Err(factors) => Value::lazy(LazySet::Product(factors.into())),
        };
        if is_lazy || env.keep_lazy || !domain.is_enumerable() {
            return Ok(self.lazy_function(bounds, body, domain, env));
        }
        let is_reducible =
            matches!(domain, Value::Set(_) | Value::MixedSet(_) | Value::Interval(..));
        match self.enumerated_function(bounds, sets, body, expr, env) {
            // TLC builds a function over any other domain lazily, so its body fails only where
            // the function is applied.
            Err(_) if !is_reducible => Ok(self.lazy_function(bounds, body, domain, env)),
            result => result,
        }
    }

    fn enumerated_function(
        &self,
        bounds: &[Bound],
        sets: Vec<Value>,
        body: &Expr,
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let mut variables = Vec::new();
        for (bound, set) in bounds.iter().zip(sets) {
            let elements = self.bound_elements(set, &bound.set, env)?;
            for binder in binders(&bound.pattern) {
                variables.push(Variable { binder, elements: elements.clone(), set: &bound.set });
            }
        }
        let mut pairs = Vec::new();
        self.for_each_binding(&variables, env, |env, indexes| {
            let mut key: Vec<Value> = variables
                .iter()
                .zip(indexes)
                .map(|(variable, &index)| variable.elements.get(index))
                .collect();
            let key = if key.len() == 1 { key.pop().unwrap() } else { Value::tuple(key) };
            pairs.push((key, self.eval(body, env)?));
            Ok(false)
        })?;
        Value::function(pairs).at(self, env, expr)
    }

    fn lazy_function(&self, bounds: &[Bound], body: &Expr, domain: Value, env: &Env<'_>) -> Value {
        let evaluator = self.clone();
        let captured = env.capture();
        // SAFETY: every expression this evaluator evaluates is part of its spec.
        let (bounds, body) =
            unsafe { (SpecRef::new(&self.spec, bounds), SpecRef::new(&self.spec, body)) };
        let apply = Arc::new(move |argument: &Value| {
            let mut env = captured.env();
            bind_argument(bounds.get(), argument, &mut env)?;
            evaluator.eval(body.get(), &mut env).map_err(|error| Error(error.message))
        });
        Value::LazyFunc(Arc::new(LazyFunc { domain, apply }))
    }

    /// The value of `f[x \in S] == body`. A function definition that refers to itself, or one
    /// in a `LET`, is lazy, so that its recursion stops at the arguments it is applied to.
    pub(super) fn function_definition(
        &self,
        def: DefId,
        bounds: &[Bound],
        body: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let is_lazy = self.is_recursive[def.index()] || self.spec.def(def).depth > 0;
        self.function(bounds, body, body, env, is_lazy)
    }

    /// `f[args]`, which applies `f` to the tuple of its arguments when there are several.
    #[inline(never)]
    pub(super) fn apply(
        &self,
        func: &Expr,
        args: &[Expr],
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let keep_lazy = std::mem::replace(&mut env.keep_lazy, true);
        let function = self.eval(func, env);
        env.keep_lazy = keep_lazy;
        let function = function?;
        if !function.is_function() {
            let message =
                format!("A non-function ({}) was applied as a function.", describe(&function));
            return Err(self.error(env, expr, message));
        }
        let argument = match args {
            [arg] => self.eval(arg, env)?,
            _ => Value::tuple(self.eval_all(args, env)?),
        };
        function.apply(&argument).at(self, env, expr)
    }

    /// `r.field`.
    #[inline(never)]
    pub(super) fn dot(
        &self,
        record: &Expr,
        field: Symbol,
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let value = self.eval(record, env)?;
        let message = match &value {
            Value::Tuple(_) => format!(
                "Attempted to apply function with integer domain to the non-integer argument \"{field}\""
            ),
            Value::Func(func) if func.keys.iter().all(|key| matches!(key, Value::Str(_))) => {
                match func
                    .keys
                    .iter()
                    .position(|key| matches!(key, Value::Str(name) if *name == field))
                {
                    Some(index) => return Ok(func.values[index].clone()),
                    None => format!(
                        "Attempted to select nonexistent field \"{field}\" from the record\n{value}"
                    ),
                }
            }
            Value::Func(_) | Value::LazyFunc(_) => {
                return value.apply(&Value::Str(field)).at(self, env, expr);
            }
            _ => format!("Attempted to select field \"{field}\" from a non-record value {value}"),
        };
        Err(self.error(env, expr, message))
    }

    /// `[base EXCEPT !path = value, ...]`, where `@` in each value reads the slot the old value
    /// is written to.
    #[inline(never)]
    pub(super) fn except(
        &self,
        base: &Expr,
        updates: &[ExceptUpdate],
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let mut current = self.eval(base, env)?;
        for update in updates {
            let path = update
                .path
                .iter()
                .map(|key| match key {
                    ExceptKey::Apply(args) => Ok(Key::Apply(match &args[..] {
                        [arg] => self.eval(arg, env)?,
                        _ => Value::tuple(self.eval_all(args, env)?),
                    })),
                    ExceptKey::Field(name) => Ok(Key::Field(*name)),
                })
                .collect::<Result<Vec<_>>>()?;
            let mut failure: Option<EvalError> = None;
            let updated = current.except(&path, &mut |old| {
                env.set(update.at, old.clone());
                self.eval(&update.value, env).map_err(|error| {
                    let message = error.message.clone();
                    failure = Some(error);
                    Error(message)
                })
            });
            if let Some(error) = failure {
                return Err(error);
            }
            current = updated.at(self, env, expr)?;
        }
        Ok(current)
    }
}

/// Binds the argument a lazy function is applied to: a value for one bound variable, or a
/// tuple with a component for each.
fn bind_argument(bounds: &[Bound], argument: &Value, env: &mut Env<'_>) -> tla_value::Result<()> {
    let binders: Vec<Binder<'_>> =
        bounds.iter().flat_map(|bound| binders(&bound.pattern)).collect();
    if let [binder] = binders[..] {
        return bind(binder, argument.clone(), env);
    }
    let Some(items) = tuple_items(argument).filter(|items| items.len() >= binders.len()) else {
        return Err(Error(
            "Attempted to apply a function to an argument not in its domain.".to_owned(),
        ));
    };
    for (binder, item) in binders.into_iter().zip(items.iter()) {
        bind(binder, item.clone(), env)?;
    }
    Ok(())
}

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
