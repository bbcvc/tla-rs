//! Functions: construction, function definitions, application, field selection, and `EXCEPT`.

use std::sync::Arc;

use tla_resolve::{Bound, DefBody, DefId, ExceptKey, ExceptUpdate, Expr, ExprKind, Scope};
use tla_value::{Error, Key, LazyFunc, LazySet, Symbol, Value};

use super::bound::{Binder, Variable, bind_frame, binders, tuple_items};
use super::{At, describe};
use crate::env::{Captured, Env, Frame, SpecRef};
use crate::{EvalError, Evaluator, Result};

/// The parameters, body, and scope of a function that TLC keeps lazy, which successor
/// generation walks when an action applies the function, as TLC walks a `FcnLambdaValue`.
pub(crate) struct Lambda {
    pub bounds: SpecRef<[Bound]>,
    pub body: SpecRef<Expr>,
    pub captured: Captured,
}

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
        let lambda = Arc::new(Lambda {
            // SAFETY: every expression this evaluator evaluates is part of its spec.
            bounds: unsafe { SpecRef::new(&self.spec, bounds) },
            body: unsafe { SpecRef::new(&self.spec, body) },
            captured: env.capture(),
        });
        let source: Arc<dyn std::any::Any + Send + Sync> = lambda.clone();
        let apply = Arc::new(move |argument: &Value| {
            let mut env = lambda.captured.env();
            bind_argument(lambda.bounds.get(), argument, &mut env.frame)?;
            evaluator.eval(lambda.body.get(), &mut env).map_err(|error| Error(error.message))
        });
        Value::LazyFunc(Arc::new(LazyFunc { domain, apply, source: Some(source) }))
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
        if let ExprKind::Call { def, scope, args: call_args } = &func.kind
            && call_args.is_empty()
            && self.is_applied_in_place(*def)
        {
            return self.apply_definition(*def, scope, args, expr, env);
        }
        let keep_lazy = std::mem::replace(&mut env.keep_lazy, true);
        let function = self.eval(func, env);
        env.keep_lazy = keep_lazy;
        let function = function?;
        if !function.is_function() {
            let message = format!(
                "A non-function ({}) was applied as a function.\n{}",
                describe(&function),
                self.range(env, expr)
            );
            return Err(self.error(env, expr, message));
        }
        let argument = match args {
            [arg] => self.eval(arg, env)?,
            _ => Value::tuple(self.eval_all(args, env)?),
        };
        function.apply(&argument).at(self, env, expr)
    }

    /// Whether applying `def` evaluates its body at the argument in place: `def` is a function
    /// definition the evaluator builds lazily, a recursive one or one in a `LET`, which nothing
    /// replaces.
    fn is_applied_in_place(&self, def: DefId) -> bool {
        matches!(self.spec.def(def).body, DefBody::Function { .. })
            && (self.is_recursive[def.index()] || self.spec.def(def).depth > 0)
            && self.overrides[def.index()].is_none()
            && self.natives[def.index()].is_none()
            && !self.is_computed_once(def)
    }

    /// `f[args]` for a function definition `f[x \in S] == body` that the evaluator builds lazily.
    /// It evaluates the body at the argument as the lazy function would, without building the
    /// function, which a recursive definition would otherwise do at each step of its recursion.
    fn apply_definition(
        &self,
        def: DefId,
        scope: &Scope,
        args: &[Expr],
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let info = self.spec.def(def);
        let DefBody::Function { bounds, body } = &info.body else {
            unreachable!("only a function definition is applied in place")
        };
        let parent = self.scope_frame(scope, env)?;
        let frame = Arc::new(Frame::new(Vec::new(), info.frame_size, parent));
        // As in the lazy function, which keeps the state and the laziness of its application.
        let mut inner =
            Env { frame, module: info.module, state: env.state, next: env.next, keep_lazy: true };
        let mut factors = Vec::new();
        for bound in bounds {
            let set = self.eval(&bound.set, &mut inner)?;
            factors.extend(binders(&bound.pattern).map(|_| set.clone()));
        }
        let domain = match <[Value; 1]>::try_from(factors) {
            Ok([set]) => set,
            Err(factors) => Value::lazy(LazySet::Product(factors.into())),
        };
        let argument = match args {
            [arg] => self.eval(arg, env)?,
            _ => Value::tuple(self.eval_all(args, env)?),
        };
        if !domain.contains(&argument).at(self, env, expr)? {
            let message =
                format!("Attempted to apply a function to {argument}, which is not in its domain");
            return Err(self.error(env, expr, message));
        }
        bind_argument(bounds, &argument, &mut inner.frame).at(self, env, expr)?;
        self.eval(body, &mut inner).map_err(|error| self.error(env, expr, error.message))
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
                        "Attempted to select nonexistent field \"{field}\" from the record\n{value}\n{}",
                        self.range(env, expr)
                    ),
                }
            }
            Value::Func(_) | Value::LazyFunc(_) => {
                return value.apply(&Value::Str(field)).at(self, env, expr);
            }
            _ => format!(
                "Attempted to select field \"{field}\" from a non-record value {value}\n{}",
                self.range(env, expr)
            ),
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
            let except = if env.keep_lazy { Value::except_kept_lazy } else { Value::except };
            let updated = except(&current, &path, &mut |old| {
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
pub(super) fn bind_argument(
    bounds: &[Bound],
    argument: &Value,
    frame: &mut Arc<Frame>,
) -> tla_value::Result<()> {
    if let [bound] = bounds
        && let mut single = binders(&bound.pattern)
        && let (Some(binder), None) = (single.next(), single.next())
    {
        return bind_frame(binder, argument.clone(), frame);
    }
    let binders: Vec<Binder<'_>> =
        bounds.iter().flat_map(|bound| binders(&bound.pattern)).collect();
    if let [binder] = binders[..] {
        return bind_frame(binder, argument.clone(), frame);
    }
    let Some(items) = tuple_items(argument).filter(|items| items.len() >= binders.len()) else {
        return Err(Error(
            "Attempted to apply a function to an argument not in its domain.".to_owned(),
        ));
    };
    for (binder, item) in binders.into_iter().zip(items.iter()) {
        bind_frame(binder, item.clone(), frame)?;
    }
    Ok(())
}
