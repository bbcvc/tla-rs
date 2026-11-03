//! Calls of definitions, operator parameters, and constants, and the operators passed as
//! arguments.
//!
//! TLC evaluates the arguments of a definition lazily: each becomes a [`Thunk`] that the body
//! evaluates where it reads the parameter, in the reader's state, so that `p'` for a parameter
//! `p` primes the argument expression. The arguments of a native implementation and of a
//! built-in operator are evaluated before the call.

use std::sync::{Arc, OnceLock};

use tla_resolve::{ConstId, DefBody, DefId, Expr, ExprKind, Local, OpRef, Scope};
use tla_value::{Error, Value};

use super::At;
use crate::env::{Env, Frame, Slot, SpecRef, StateRef, Thunk};
use crate::native::OperatorKind;
use crate::{Arg, ConstBinding, Ctx, EvalError, Evaluator, Native, Operator, Result};

impl Evaluator {
    /// Calls `def` with `args`, in a new frame whose parent is `parent`, unless the configuration
    /// or a native implementation replaces it.
    pub(crate) fn call_def(
        &self,
        def: DefId,
        parent: Option<Arc<Frame>>,
        args: Vec<Value>,
        state: Option<StateRef<'_>>,
        next: Option<StateRef<'_>>,
    ) -> Result<Value> {
        let info = self.spec.def(def);
        if args.len() != info.params.len() {
            let message = format!(
                "The operator {} requires {} arguments, but is applied to {}.",
                info.name,
                info.params.len(),
                args.len()
            );
            return Err(EvalError::at(&self.spec, info.module, info.span, message));
        }
        if let Some(binding) = &self.overrides[def.index()] {
            return match binding {
                ConstBinding::Value(value) => Ok(value.clone()),
                ConstBinding::Def(other) => self.call_def(*other, None, args, state, next),
                ConstBinding::Table(table) => table
                    .apply(&args)
                    .map_err(|error| EvalError::at(&self.spec, info.module, info.span, error.0)),
            };
        }
        if let Some(native) = self.natives[def.index()] {
            let args: Vec<Arg> = args.into_iter().map(Arg::Value).collect();
            let definition = || {
                let slots = args.iter().map(|arg| match arg {
                    Arg::Value(value) => Slot::Value(value.clone()),
                    Arg::Op(op) => Slot::Op(op.clone()),
                });
                self.enter(def, parent.clone(), slots.collect(), state, next, false)
            };
            let mut ctx = Ctx::new(self, state);
            ctx.next = next;
            ctx.definition = Some(&definition);
            return native(&mut ctx, &args)
                .map_err(|error| EvalError::at(&self.spec, info.module, info.span, error.0));
        }
        if args.is_empty() && self.is_computed_once(def) {
            return self.constant_value(def);
        }
        let slots = args.into_iter().map(Slot::Value).collect();
        self.enter(def, parent, slots, state, next, false)
    }

    /// Evaluates the body of `def` in a new frame holding `slots`.
    pub(super) fn enter(
        &self,
        def: DefId,
        parent: Option<Arc<Frame>>,
        slots: Vec<Slot>,
        state: Option<StateRef<'_>>,
        next: Option<StateRef<'_>>,
        keep_lazy: bool,
    ) -> Result<Value> {
        let info = self.spec.def(def);
        let frame = Arc::new(Frame::new(slots, info.frame_size, parent));
        let mut env = Env { frame, module: info.module, state, next, keep_lazy };
        match &info.body {
            DefBody::Expr(body) => self.eval(body, &mut env),
            DefBody::Function { bounds, body } => {
                self.function_definition(def, bounds, body, &mut env)
            }
        }
    }

    /// `Op(args)`, a call of a definition. A definition the configuration overrides with a value
    /// yields that value for any arguments, like an operator constant.
    pub(super) fn call(
        &self,
        def: DefId,
        scope: &Scope,
        args: &[Expr],
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        if let Some(binding) = &self.overrides[def.index()] {
            return self.call_binding(binding, args, expr, env);
        }
        let info = self.spec.def(def);
        // Where TLC doesn't normalize the argument of `TLCEval`, it applies its definition,
        // `TLCEval(v) == v`.
        if self.tlc_eval == Some(def)
            && let [arg] = args
            && !self.normalizing_evaluations.contains(&(expr as *const Expr as usize))
        {
            return self.eval(arg, env);
        }
        if let Some(native) = self.natives[def.index()] {
            return self.call_native(native, def, scope, args, expr, env);
        }
        if args.is_empty() && self.is_computed_once(def) {
            return self.constant_value(def);
        }
        if args.len() != info.params.len() {
            return Err(self.arity_error(def, args.len(), env, expr));
        }
        let parent = self.scope_frame(scope, env)?;
        let slots = args.iter().map(|arg| self.arg_slot(arg, env)).collect::<Result<Vec<_>>>()?;
        self.enter(def, parent, slots, env.state, env.next, env.keep_lazy)
    }

    #[cold]
    #[inline(never)]
    fn arity_error(&self, def: DefId, count: usize, env: &Env<'_>, expr: &Expr) -> EvalError {
        let info = self.spec.def(def);
        let message = format!(
            "The operator {} requires {} arguments, but is applied to {count}.",
            info.name,
            info.params.len()
        );
        self.error(env, expr, message)
    }

    #[inline(never)]
    fn call_native(
        &self,
        native: Native,
        def: DefId,
        scope: &Scope,
        args: &[Expr],
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let takes_expressions = self.takes_expressions[def.index()];
        let arg_exprs = args;
        let args = self
            .spec
            .def(def)
            .params
            .iter()
            .zip(args)
            .map(|(&arity, arg)| match (arity, &arg.kind) {
                (0, _) if takes_expressions => Ok(Arg::Op(self.deferred(arg, env))),
                (0, _) => Ok(Arg::Value(self.eval(arg, env)?)),
                (_, ExprKind::OpArg(op)) => Ok(Arg::Op(self.operator(op, arg, env)?)),
                _ => Err(self.error(env, arg, "Expected an operator as this argument")),
            })
            .collect::<Result<Vec<_>>>()?;
        let outer: &Env<'_> = env;
        let definition = || {
            let parent = self.scope_frame(scope, outer)?;
            let slots = arg_exprs.iter().map(|arg| self.arg_slot(arg, outer));
            let slots = slots.collect::<Result<_>>()?;
            self.enter(def, parent, slots, outer.state, outer.next, outer.keep_lazy)
        };
        let mut ctx = Ctx::new(self, env.state);
        ctx.next = env.next;
        ctx.definition = Some(&definition);
        let result = native(&mut ctx, &args);
        result.at(self, env, expr)
    }

    /// `F(args)` for an operator parameter `F`.
    #[inline(never)]
    pub(super) fn call_param(
        &self,
        param: Local,
        args: &[Expr],
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let Slot::Op(op) = env.slot(param.hops, param.slot) else {
            return Err(self.error(env, expr, "Expected an operator but found a value"));
        };
        let op = op.clone();
        if let OperatorKind::Def { def, parent } = &op.0
            && self.natives[def.index()].is_none()
            && self.overrides[def.index()].is_none()
        {
            if args.len() != self.spec.def(*def).params.len() {
                return Err(self.arity_error(*def, args.len(), env, expr));
            }
            let slots =
                args.iter().map(|arg| self.arg_slot(arg, env)).collect::<Result<Vec<_>>>()?;
            return self.enter(*def, parent.clone(), slots, env.state, env.next, env.keep_lazy);
        }
        let values = self.eval_all(args, env)?;
        self.apply_operator(&op, &values, env.state, env.next).at(self, env, expr)
    }

    /// Applies an operator to values.
    pub(crate) fn apply_operator(
        &self,
        op: &Operator,
        args: &[Value],
        state: Option<StateRef<'_>>,
        next: Option<StateRef<'_>>,
    ) -> tla_value::Result<Value> {
        match &op.0 {
            OperatorKind::Def { def, parent } => self
                .call_def(*def, parent.clone(), args.to_vec(), state, next)
                .map_err(|error| Error(error.message)),
            OperatorKind::Builtin(builtin) => self.apply_builtin(*builtin, args),
            OperatorKind::Closure(apply) => {
                let mut ctx = Ctx::new(self, state);
                ctx.next = next;
                apply(&mut ctx, args)
            }
        }
    }

    /// A constant without parameters.
    #[inline(never)]
    pub(super) fn constant(&self, id: ConstId, expr: &Expr, env: &mut Env<'_>) -> Result<Value> {
        self.call_const(id, &[], expr, env)
    }

    /// `F(args)` for a constant operator `F`.
    #[inline(never)]
    pub(super) fn call_const(
        &self,
        id: ConstId,
        args: &[Expr],
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        match self.constants.get(id.index()) {
            Some(binding) => self.call_binding(binding, args, expr, env),
            None => Err(self.error(env, expr, self.unbound(id))),
        }
    }

    /// Applies what the configuration binds a constant or definition to. TLC takes a value as
    /// the value of the operator applied to any arguments.
    fn call_binding(
        &self,
        binding: &ConstBinding,
        args: &[Expr],
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        match binding {
            ConstBinding::Value(value) => Ok(value.clone()),
            ConstBinding::Def(def) => self.call(*def, &Scope::Global, args, expr, env),
            ConstBinding::Table(table) => {
                let values = self.eval_all(args, env)?;
                table.apply(&values).at(self, env, expr)
            }
        }
    }

    fn unbound(&self, id: ConstId) -> String {
        let name = self.spec.constants[id.index()].name;
        format!("The constant parameter {name} is not assigned a value by the configuration file.")
    }

    /// The frame a definition called with `scope` captures.
    pub(super) fn scope_frame(&self, scope: &Scope, env: &Env<'_>) -> Result<Option<Arc<Frame>>> {
        Ok(match scope {
            Scope::Global => None,
            Scope::Up(hops) => Some(env.frame.up(*hops).clone()),
            Scope::Instance { parent, args } => {
                let parent = self.scope_frame(parent, env)?;
                let slots =
                    args.iter().map(|arg| self.arg_slot(arg, env)).collect::<Result<Vec<_>>>()?;
                Some(Arc::new(Frame::new(slots, args.len(), parent)))
            }
        })
    }

    /// What the parameter an argument is passed to holds: the operator it stands for, the value
    /// of a literal or of a slot already evaluated, or else a thunk.
    pub(super) fn arg_slot(&self, arg: &Expr, env: &Env<'_>) -> Result<Slot> {
        Ok(match &arg.kind {
            ExprKind::OpArg(op) => Slot::Op(self.operator(op, arg, env)?),
            ExprKind::Bool(value) => Slot::Value(Value::Bool(*value)),
            ExprKind::Str(text) => Slot::Value(Value::Str(*text)),
            ExprKind::Int(value) => Slot::Value(self.int(*value, arg, env)?),
            ExprKind::Local(local) => env.slot(local.hops, local.slot).clone(),
            ExprKind::Const(id) => match self.constants.get(id.index()) {
                Some(ConstBinding::Value(value)) => Slot::Value(value.clone()),
                _ => self.thunk(arg, env),
            },
            _ => self.thunk(arg, env),
        })
    }

    fn thunk(&self, arg: &Expr, env: &Env<'_>) -> Slot {
        Slot::Thunk(Arc::new(Thunk {
            // SAFETY: every expression this evaluator evaluates is part of its spec.
            expr: unsafe { SpecRef::new(&self.spec, arg) },
            captured: env.capture_scope(),
            value: OnceLock::new(),
        }))
    }

    /// An argument a native evaluates itself, if at all: an operator without parameters that
    /// evaluates the expression where the call is.
    fn deferred(&self, arg: &Expr, env: &Env<'_>) -> Operator {
        let evaluator = self.clone();
        // SAFETY: every expression this evaluator evaluates is part of its spec.
        let arg = unsafe { SpecRef::new(&self.spec, arg) };
        let captured = env.capture();
        Operator::closure(move |_, _| {
            evaluator.eval(arg.get(), &mut captured.env()).map_err(|error| Error(error.message))
        })
    }

    /// The value of an argument a parameter holds, in the states of `env`.
    #[inline(never)]
    pub(super) fn force(&self, thunk: &Thunk, expr: &Expr, env: &Env<'_>) -> Result<Value> {
        if !Arc::ptr_eq(thunk.expr.spec(), &self.spec) {
            return Err(self.error(env, expr, "An argument of another specification was read"));
        }
        let is_cached = thunk.captured.is_in_states_of(env);
        if is_cached && let Some(value) = thunk.value.get() {
            return Ok(value.clone());
        }
        let mut inner = Env {
            frame: thunk.captured.frame.clone(),
            module: thunk.captured.module,
            state: env.state,
            next: env.next,
            keep_lazy: env.keep_lazy,
        };
        let value = self.eval(thunk.expr.get(), &mut inner)?;
        if is_cached {
            let _ = thunk.value.set(value.clone());
        }
        Ok(value)
    }

    /// The operator an argument for a parameter such as `F(_)` stands for.
    pub(super) fn operator(&self, op: &OpRef, expr: &Expr, env: &Env<'_>) -> Result<Operator> {
        let kind = match op {
            OpRef::Def { def, scope } => {
                OperatorKind::Def { def: *def, parent: self.scope_frame(scope, env)? }
            }
            OpRef::Param(local) => {
                return match env.slot(local.hops, local.slot) {
                    Slot::Op(op) => Ok(op.clone()),
                    _ => Err(self.error(env, expr, "Expected an operator but found a value")),
                };
            }
            OpRef::Const(id) => match self.constants.get(id.index()) {
                Some(ConstBinding::Def(def)) => OperatorKind::Def { def: *def, parent: None },
                Some(ConstBinding::Value(value)) => {
                    let value = value.clone();
                    return Ok(Operator::closure(move |_, _| Ok(value.clone())));
                }
                Some(ConstBinding::Table(table)) => {
                    let table = table.clone();
                    return Ok(Operator::closure(move |_, args| table.apply(args)));
                }
                None => return Err(self.error(env, expr, self.unbound(*id))),
            },
            OpRef::Builtin(builtin) => OperatorKind::Builtin(*builtin),
        };
        Ok(Operator(kind))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use tla_resolve::RootName;
    use tla_value::{Result, Value};

    use crate::{Arg, Ctx, Evaluator, Operator};

    /// `Map(F, S)`: the set of `F(x)` for each `x` in `S`, as a native would compute it.
    fn map(ctx: &mut Ctx<'_>, args: &[Arg]) -> Result<Value> {
        let op = args[0].op()?;
        let mut mapped = Vec::new();
        for element in args[1].value()?.elements()?.iter() {
            mapped.push(ctx.call(op, std::slice::from_ref(element))?);
        }
        Value::set(mapped)
    }

    /// `Wrapped(x)`: applies a Rust operator through the context.
    fn wrapped(ctx: &mut Ctx<'_>, args: &[Arg]) -> Result<Value> {
        let pair = Operator::closure(|_, args| Ok(Value::tuple(args.to_vec())));
        ctx.call(&pair, &[args[0].value()?.clone()])
    }

    /// `Declined(x)`: falls back to its definition, as a Java override that returns `null` does.
    fn declined(ctx: &mut Ctx<'_>, _: &[Arg]) -> Result<Value> {
        ctx.evaluate_definition()
    }

    fn evaluator_with_natives(source: &str) -> Evaluator {
        let spec = tla_resolve::resolve(source, &mut |_name: &str| None).unwrap();
        let mut evaluator = Evaluator::new(Arc::new(spec), Vec::new());
        let mut natives = evaluator.natives.to_vec();
        let replaced =
            [("Map", map as crate::Native), ("Wrapped", wrapped), ("Declined", declined)];
        for (name, native) in replaced {
            if let Some(RootName::Def(def)) = evaluator.spec.lookup(name) {
                natives[def.index()] = Some(native);
            }
        }
        evaluator.natives = natives.into();
        evaluator
    }

    #[test]
    fn falls_back_to_the_definition_a_native_replaces() {
        let evaluator = evaluator_with_natives(
            r#"
---- MODULE Natives ----
Map(F(_), S) == {}
Wrapped(x) == x
Declined(x) == <<x, x>>
Call(p) == <<Declined(<<p>>), Map(Declined, {3})>>
Expr == Call(1)
====
"#,
        );
        let Some(RootName::Def(def)) = evaluator.spec.lookup("Expr") else { panic!() };
        assert_eq!(
            evaluator.eval_def(def, None).unwrap().to_string(),
            "<<<<<<1>>, <<1>>>>, {<<3, 3>>}>>"
        );
    }

    #[test]
    fn calls_natives_with_values_and_operators() {
        let evaluator = evaluator_with_natives(
            r#"
---- MODULE Natives ----
Map(F(_), S) == {}
Wrapped(x) == x
Lift(x) == {x}
Expr(p) == <<Map(Lift, {1, 2}), Map(LAMBDA x : <<x, p>>, {3}), Map(SUBSET, {{}}), Wrapped(4)>>
Call == Expr(9)
====
"#,
        );
        let Some(RootName::Def(def)) = evaluator.spec.lookup("Call") else { panic!() };
        assert_eq!(
            evaluator.eval_def(def, None).unwrap().to_string(),
            "<<{{1}, {2}}, {<<3, 9>>}, {{{}}}, <<4>>>>"
        );
    }
}
