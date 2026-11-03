//! Evaluation of resolved expressions.
//!
//! An expression is evaluated in an [`Env`]: the frame of the definition whose body holds it,
//! and the current and next states. Errors are worded as TLC words them, following tla-ts, and
//! located at the innermost expression that failed.

mod action;
mod analysis;
mod bound;
mod builtin;
mod call;
mod function;

use tla_ast::{Quantifier, Span};
use tla_resolve::{DefId, Expr, ExprKind, Local, ModuleId, VarId};
use tla_value::{LazySet, Symbol, Value};

pub use self::action::NextAction;
pub(crate) use self::analysis::{normalizing_evaluations, recursive_functions, tlc_eval};
use self::builtin::describe;
use crate::env::{Env, Slot, StateRef};
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
        self.call_def(
            def,
            None,
            Vec::new(),
            state.map(StateRef::Complete),
            next.map(StateRef::Complete),
        )
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
            ExprKind::OpArg(_) => self.fail_at(env, expr, "An operator cannot be used as a value"),
            ExprKind::And(items) => self.junction(true, items, expr, env),
            ExprKind::Or(items) => self.junction(false, items, expr, env),
            ExprKind::If { cond, then, otherwise } => {
                self.condition(cond, then, otherwise, expr, env)
            }
            ExprKind::Case { arms, other } => self.case(arms, other.as_deref(), expr, env),
            ExprKind::Quant { quantifier, bounds, body } => {
                self.quantifier(*quantifier, bounds, body, expr, env)
            }
            ExprKind::UnboundedQuant { quantifier, .. } => match quantifier {
                Quantifier::Forall | Quantifier::Exists => {
                    self.fail_at(env, expr, "TLC cannot evaluate an unbounded quantifier")
                }
                Quantifier::TemporalForall | Quantifier::TemporalExists => {
                    self.fail_at(env, expr, TEMPORAL_ERROR)
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
            ExprKind::Fairness { .. } => self.fail_at(env, expr, TEMPORAL_ERROR),
        }
    }

    /// Fails with `message` followed by where the expression starts, as TLC words it.
    #[cold]
    #[inline(never)]
    fn fail_at(&self, env: &Env<'_>, expr: &Expr, message: &str) -> Result<Value> {
        Err(self.error(env, expr, format!("{message} at {}", self.location(env, expr))))
    }

    /// Where an expression starts, as tla-ts's `describeLocation` puts it in a message.
    pub(crate) fn location(&self, env: &Env<'_>, expr: &Expr) -> String {
        let (line, column) = expr.span.line_column(&self.spec.modules[env.module.index()].source);
        format!("line {line}, column {column}")
    }

    /// Where an expression is, as SANY describes a location in TLC's messages:
    /// `line 1, col 2 to line 3, col 4 of module M`, the end being the last character.
    pub(crate) fn range(&self, env: &Env<'_>, expr: &Expr) -> String {
        self.range_of(env.module, expr.span)
    }

    /// Where `span` of `module` is, as [`Evaluator::range`] describes it.
    pub(crate) fn range_of(&self, module: ModuleId, span: Span) -> String {
        let module = &self.spec.modules[module.index()];
        let (line, column) = span.line_column(&module.source);
        let last = span.end.saturating_sub(1).max(span.start) as usize;
        let (end_line, end_column) = Span::new(last, last + 1).line_column(&module.source);
        format!(
            "line {line}, col {column} to line {end_line}, col {end_column} of module {}",
            module.name
        )
    }

    /// How SANY describes an expression in a message: a numeral as written, and any other
    /// expression by its range.
    pub(crate) fn node(&self, env: &Env<'_>, expr: &Expr) -> String {
        match expr.kind {
            ExprKind::Int(_) => {
                let source = &self.spec.modules[env.module.index()].source;
                source[expr.span.start as usize..expr.span.end as usize].to_owned()
            }
            _ => self.range(env, expr),
        }
    }

    fn condition(
        &self,
        cond: &Expr,
        then: &Expr,
        otherwise: &Expr,
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        match self.eval(cond, env)? {
            Value::Bool(true) => self.eval(then, env),
            Value::Bool(false) => self.eval(otherwise, env),
            value => {
                let message = format!(
                    "A non-boolean expression ({}) was used as the condition of an IF.\n{}",
                    describe(&value),
                    self.range(env, expr)
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
            let message = format!(
                "TLC can't handle a number this big: {} at {}",
                self.node(env, expr),
                self.location(env, expr)
            );
            self.error(env, expr, message)
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
                        "In evaluation, the identifier {name} is either undefined or not an operator.\n{}",
                        self.range(env, expr)
                    ),
                ))
            }
        }
    }

    fn local(&self, local: Local, expr: &Expr, env: &Env<'_>) -> Result<Value> {
        match env.slot(local.hops, local.slot) {
            Slot::Value(value) => Ok(value.clone()),
            Slot::Thunk(thunk) => self.force(thunk, expr, env),
            Slot::Op(_) => self.fail_at(env, expr, "An operator cannot be used as a value"),
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
                                "A non-boolean expression ({kind}) was used as a formula in a {formula}.\n{}",
                                self.node(env, item)
                            ),
                        )
                    } else {
                        let (operator, side) = (
                            if is_and { "/\\" } else { "\\/" },
                            if index == 0 { "P" } else { "Q" },
                        );
                        // TLC nests an infix chain to the left, so the junction that fails ends
                        // with the operand that failed, or the second one.
                        let end = items[index.max(1).min(items.len() - 1)].span.end;
                        let junction = Expr::new(
                            ExprKind::Bool(false),
                            Span::new(expr.span.start as usize, end as usize),
                        );
                        self.error(
                            env,
                            expr,
                            format!(
                                "Attempted to evaluate an expression of form P {operator} Q when {side} was\n{kind}.\n{}",
                                self.range(env, &junction)
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
                        "A non-boolean expression ({}) was used as a condition of a CASE. {}",
                        describe(&value),
                        self.node(env, guard)
                    );
                    return Err(self.error(env, guard, message));
                }
            }
        }
        match other {
            Some(other) => self.eval(other, env),
            None => {
                let message = format!(
                    "Attempted to evaluate a CASE with no conditions true.\n{}",
                    self.range(env, expr)
                );
                Err(self.error(env, expr, message))
            }
        }
    }

    /// `e'`: `e` evaluated in the next state.
    fn prime(&self, operand: &Expr, expr: &Expr, env: &mut Env<'_>) -> Result<Value> {
        let Some(next) = env.next else {
            let message = format!(
                "A primed expression appears outside an action at {}",
                self.location(env, expr)
            );
            return Err(self.error(env, expr, message));
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
