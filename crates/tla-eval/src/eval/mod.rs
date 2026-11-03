//! Evaluation of resolved expressions.
//!
//! An expression is evaluated in an [`Env`]: the frame of the definition whose body holds it,
//! and the current and next states. Errors are worded as TLC words them, following tla-ts, and
//! located at the innermost expression that failed.

mod bound;
mod builtin;
mod call;
mod function;

use tla_ast::Quantifier;
use tla_resolve::{DefId, Expr, ExprKind, Local, VarId};
use tla_value::{LazySet, Symbol, Value};

use self::builtin::describe;
pub(crate) use self::function::recursive_functions;
use crate::env::{Env, Slot};
use crate::{EvalError, Evaluator, Result, State};

/// Converts the error of a value operation into an [`EvalError`] at the expression that failed.
trait At<T> {
    fn at(self, evaluator: &Evaluator, env: &Env<'_>, expr: &Expr) -> Result<T>;
}

impl<T> At<T> for tla_value::Result<T> {
    fn at(self, evaluator: &Evaluator, env: &Env<'_>, expr: &Expr) -> Result<T> {
        self.map_err(|error| evaluator.error(env, expr, error.0))
    }
}

const TEMPORAL_ERROR: &str = "TLC cannot evaluate a temporal formula in a state";

impl Evaluator {
    /// Evaluates a module-level definition without parameters.
    pub(crate) fn eval_zero_arity(
        &self,
        def: DefId,
        state: Option<&State>,
        next: Option<&State>,
    ) -> Result<Value> {
        let info = self.spec.def(def);
        let problem = if info.depth > 0 {
            Some(format!("{} is defined inside another definition.", info.name))
        } else if !info.params.is_empty() {
            Some(format!("The operator {} requires {} arguments.", info.name, info.params.len()))
        } else {
            None
        };
        if let Some(message) = problem {
            return Err(EvalError::at(&self.spec, info.module, info.span, message));
        }
        self.call_def(def, None, Vec::new(), state, next)
    }

    pub(crate) fn error(
        &self,
        env: &Env<'_>,
        expr: &Expr,
        message: impl Into<String>,
    ) -> EvalError {
        EvalError::at(&self.spec, env.module, expr.span, message)
    }

    pub(crate) fn eval(&self, expr: &Expr, env: &mut Env<'_>) -> Result<Value> {
        match &expr.kind {
            ExprKind::Bool(value) => Ok(Value::Bool(*value)),
            ExprKind::Int(value) => self.int(*value, expr, env),
            ExprKind::Str(text) => Ok(Value::Str(*text)),
            ExprKind::Var(id) => self.var(*id, expr, env),
            ExprKind::Const(id) => self.constant(*id, expr, env),
            ExprKind::Local(local) => self.local(*local, expr, env),
            ExprKind::Call { def, scope, args } => self.call(*def, scope, args, expr, env),
            ExprKind::CallParam { param, args } => self.call_param(*param, args, expr, env),
            ExprKind::CallConst { id, args } => self.call_const(*id, args, expr, env),
            ExprKind::Builtin { op, args } => self.builtin(*op, args, expr, env),
            ExprKind::OpArg(_) => self.fail(env, expr, "An operator cannot be used as a value"),
            ExprKind::And(items) => self.junction(true, items, expr, env),
            ExprKind::Or(items) => self.junction(false, items, expr, env),
            ExprKind::If { cond, then, otherwise } => self.condition(cond, then, otherwise, env),
            ExprKind::Case { arms, other } => self.case(arms, other.as_deref(), expr, env),
            ExprKind::Quant { quantifier, bounds, body } => {
                self.quantifier(*quantifier, bounds, body, expr, env)
            }
            ExprKind::UnboundedQuant { quantifier, .. } => match quantifier {
                Quantifier::Forall | Quantifier::Exists => {
                    self.fail(env, expr, "TLC cannot evaluate an unbounded quantifier")
                }
                Quantifier::TemporalForall | Quantifier::TemporalExists => {
                    self.fail(env, expr, TEMPORAL_ERROR)
                }
            },
            ExprKind::Choose { pattern, set, body } => {
                self.choose(pattern, set.as_deref(), body, expr, env)
            }
            ExprKind::SetEnum(items) => self.set_enum(items, expr, env),
            ExprKind::SetFilter { bound, pred } => self.set_filter(bound, pred, expr, env),
            ExprKind::SetMap { body, bounds } => self.set_map(bounds, body, expr, env),
            ExprKind::Tuple(items) => self.eval_all(items, env).map(Value::tuple),
            ExprKind::Record(fields) => self.record(fields, env),
            ExprKind::RecordSet(fields) => self.record_set(fields, env),
            ExprKind::FuncSet { domain, range } => self.function_set(domain, range, env),
            ExprKind::Function { bounds, body } => self.function(bounds, body, expr, env, false),
            ExprKind::FuncApp { func, args } => self.apply(func, args, expr, env),
            ExprKind::Dot { record, field } => self.dot(record, *field, expr, env),
            ExprKind::Except { base, updates } => self.except(base, updates, expr, env),
            ExprKind::Product(factors) => self.product(factors, env),
            ExprKind::BoxAction { action, sub } => {
                self.subscripted_action(true, action, sub, expr, env)
            }
            ExprKind::AngleAction { action, sub } => {
                self.subscripted_action(false, action, sub, expr, env)
            }
            ExprKind::Fairness { .. } => self.fail(env, expr, TEMPORAL_ERROR),
        }
    }

    #[cold]
    #[inline(never)]
    fn fail(&self, env: &Env<'_>, expr: &Expr, message: &str) -> Result<Value> {
        Err(self.error(env, expr, message))
    }

    fn condition(
        &self,
        cond: &Expr,
        then: &Expr,
        otherwise: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        match self.eval(cond, env)? {
            Value::Bool(true) => self.eval(then, env),
            Value::Bool(false) => self.eval(otherwise, env),
            value => {
                let message = format!(
                    "A non-boolean expression ({}) was used as the condition of an IF.",
                    describe(&value)
                );
                Err(self.error(env, cond, message))
            }
        }
    }

    #[inline(never)]
    fn set_enum(&self, items: &[Expr], expr: &Expr, env: &mut Env<'_>) -> Result<Value> {
        let elements = self.eval_all(items, env)?;
        Value::set(elements).at(self, env, expr)
    }

    #[inline(never)]
    fn record(&self, fields: &[(Symbol, Expr)], env: &mut Env<'_>) -> Result<Value> {
        let fields = fields
            .iter()
            .map(|(name, value)| Ok((*name, self.eval(value, env)?)))
            .collect::<Result<Vec<_>>>()?;
        Ok(Value::record(fields))
    }

    /// `[a : S, b : T]`, with its fields sorted by name.
    #[inline(never)]
    fn record_set(&self, fields: &[(Symbol, Expr)], env: &mut Env<'_>) -> Result<Value> {
        let mut fields = fields
            .iter()
            .map(|(name, set)| Ok((*name, self.eval(set, env)?)))
            .collect::<Result<Vec<_>>>()?;
        fields.sort_by_key(|(name, _)| *name);
        Ok(Value::lazy(LazySet::RecordSet(fields.into())))
    }

    #[inline(never)]
    fn function_set(&self, domain: &Expr, range: &Expr, env: &mut Env<'_>) -> Result<Value> {
        let domain = self.eval(domain, env)?;
        let range = self.eval(range, env)?;
        Ok(Value::lazy(LazySet::FuncSet { domain, range }))
    }

    #[inline(never)]
    fn product(&self, factors: &[Expr], env: &mut Env<'_>) -> Result<Value> {
        Ok(Value::lazy(LazySet::Product(self.eval_all(factors, env)?.into())))
    }

    fn eval_all(&self, exprs: &[Expr], env: &mut Env<'_>) -> Result<Vec<Value>> {
        exprs.iter().map(|expr| self.eval(expr, env)).collect()
    }

    fn int(&self, value: i64, expr: &Expr, env: &Env<'_>) -> Result<Value> {
        i32::try_from(value).map(Value::Int).map_err(|_| {
            self.error(env, expr, format!("TLC can't handle a number this big: {value}"))
        })
    }

    fn var(&self, id: VarId, expr: &Expr, env: &Env<'_>) -> Result<Value> {
        match env.state.and_then(|state| state.get(id.index())) {
            Some(value) => Ok(value.clone()),
            None => {
                let name = self.spec.variables[id.index()].name;
                Err(self.error(
                    env,
                    expr,
                    format!(
                        "In evaluation, the identifier {name} is either undefined or not an operator."
                    ),
                ))
            }
        }
    }

    fn local(&self, local: Local, expr: &Expr, env: &Env<'_>) -> Result<Value> {
        match env.slot(local.hops, local.slot) {
            Slot::Value(value) => Ok(value.clone()),
            Slot::Thunk(thunk) => self.force(thunk, expr, env),
            Slot::Op(_) => Err(self.error(env, expr, "An operator cannot be used as a value")),
        }
    }

    /// A conjunction (`is_and`) or disjunction, evaluated left to right until one operand
    /// decides it.
    #[inline(never)]
    fn junction(
        &self,
        is_and: bool,
        items: &[Expr],
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        for (index, item) in items.iter().enumerate() {
            match self.eval(item, env)? {
                Value::Bool(value) if value != is_and => return Ok(Value::Bool(value)),
                Value::Bool(_) => {}
                value => {
                    let kind = describe(&value);
                    let source = &self.spec.modules[env.module.index()].source;
                    let text = source.get(expr.span.start as usize..).unwrap_or_default();
                    let is_bulleted = ["/\\", "\\/", "\\land", "\\lor"]
                        .iter()
                        .any(|bullet| text.starts_with(bullet));
                    return Err(if is_bulleted {
                        let formula = if is_and { "conjunction" } else { "disjunction" };
                        self.error(
                            env,
                            item,
                            format!(
                                "A non-boolean expression ({kind}) was used as a formula in a {formula}."
                            ),
                        )
                    } else {
                        let (operator, side) = (
                            if is_and { "/\\" } else { "\\/" },
                            if index == 0 { "P" } else { "Q" },
                        );
                        self.error(
                            env,
                            expr,
                            format!(
                                "Attempted to evaluate an expression of form P {operator} Q when {side} was\n{kind}."
                            ),
                        )
                    });
                }
            }
        }
        Ok(Value::Bool(is_and))
    }

    #[inline(never)]
    fn case(
        &self,
        arms: &[(Expr, Expr)],
        other: Option<&Expr>,
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        for (guard, body) in arms {
            match self.eval(guard, env)? {
                Value::Bool(true) => return self.eval(body, env),
                Value::Bool(false) => {}
                value => {
                    let message = format!(
                        "A non-boolean expression ({}) was used as a condition of a CASE.",
                        describe(&value)
                    );
                    return Err(self.error(env, guard, message));
                }
            }
        }
        match other {
            Some(other) => self.eval(other, env),
            None => {
                Err(self.error(env, expr, "Attempted to evaluate a CASE with no conditions true."))
            }
        }
    }

    /// `e'`: `e` evaluated in the next state.
    fn prime(&self, operand: &Expr, expr: &Expr, env: &mut Env<'_>) -> Result<Value> {
        let Some(next) = env.next else {
            return Err(self.error(env, expr, "A primed expression appears outside an action"));
        };
        let state = env.state;
        (env.state, env.next) = (Some(next), None);
        let value = self.eval(operand, env);
        (env.state, env.next) = (state, Some(next));
        value
    }

    /// `UNCHANGED e`, which is `e' = e`.
    fn unchanged(&self, operand: &Expr, expr: &Expr, env: &mut Env<'_>) -> Result<bool> {
        let primed = self.prime(operand, expr, env)?;
        let current = self.eval(operand, env)?;
        primed.equals(&current).at(self, env, expr)
    }

    /// `[A]_v`, which is `A \/ UNCHANGED v`, or `<<A>>_v`, which is `A /\ ~UNCHANGED v`.
    #[inline(never)]
    fn subscripted_action(
        &self,
        is_box: bool,
        action: &Expr,
        sub: &Expr,
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let is_taken = match self.eval(action, env)? {
            Value::Bool(value) => value,
            value => {
                let message = format!("Expected an action to be a boolean but found {value}");
                return Err(self.error(env, action, message));
            }
        };
        if is_taken == is_box {
            return Ok(Value::Bool(is_box));
        }
        let is_unchanged = self.unchanged(sub, expr, env)?;
        Ok(Value::Bool(is_unchanged == is_box))
    }
}
