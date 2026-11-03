//! Bound variables: quantifiers, `CHOOSE`, and set comprehensions.

use std::sync::Arc;

use tla_ast::Quantifier;
use tla_resolve::{Bound, Expr, ExprKind, Pattern};
use tla_value::{Error, LazySet, Predicate, Value, bail};

use super::builtin::is_overridden;
use super::{At, TEMPORAL_ERROR};
use crate::env::{Env, Frame, Slot, SpecRef};
use crate::{Evaluator, Result};

/// How a bound variable takes an element: into one slot, or destructured into a slot per
/// component of a tuple.
#[derive(Clone, Copy)]
pub(super) enum Binder<'e> {
    Slot(usize),
    Tuple(&'e [usize]),
}

/// The binders of a pattern, one per name of `x, y \in S`.
pub(super) fn binders(pattern: &Pattern) -> impl Iterator<Item = Binder<'_>> {
    let (names, tuple) = match pattern {
        Pattern::Names(slots) => (&slots[..], None),
        Pattern::Tuple(slots) => (&[][..], Some(Binder::Tuple(slots))),
    };
    names.iter().map(|&slot| Binder::Slot(slot)).chain(tuple)
}

/// Writes `value` into the slots of `binder`.
pub(super) fn bind(binder: Binder<'_>, value: Value, env: &mut Env<'_>) -> tla_value::Result<()> {
    bind_frame(binder, value, &mut env.frame)
}

/// Writes `value` into the slots of `binder` in `frame`.
pub(super) fn bind_frame(
    binder: Binder<'_>,
    value: Value,
    frame: &mut Arc<Frame>,
) -> tla_value::Result<()> {
    match binder {
        Binder::Slot(slot) => Arc::make_mut(frame).slots[slot] = Slot::Value(value),
        Binder::Tuple(slots) => {
            let Some(items) = tuple_items(&value).filter(|items| items.len() == slots.len()) else {
                bail!(
                    "Cannot bind a tuple of {} names to {value}, which is not a tuple of that length",
                    slots.len()
                )
            };
            let frame = Arc::make_mut(frame);
            for (&slot, item) in slots.iter().zip(items.iter()) {
                frame.slots[slot] = Slot::Value(item.clone());
            }
        }
    }
    Ok(())
}

pub(super) fn tuple_items(value: &Value) -> Option<Arc<[Value]>> {
    match value {
        Value::Tuple(items) => Some(items.clone()),
        Value::LazyFunc(_) => match value.materialize().ok()? {
            Value::Tuple(items) => Some(items),
            _ => None,
        },
        _ => None,
    }
}

/// The elements a bound variable ranges over.
#[derive(Clone)]
pub(super) enum Elements {
    /// An interval, which TLC keeps as one, so that it can stop at the first witness in a large
    /// interval without listing it.
    Interval(i32, i32),
    List(Arc<[Value]>),
}

impl Elements {
    pub fn len(&self) -> usize {
        match self {
            Elements::Interval(low, high) => {
                (i64::from(*high) - i64::from(*low) + 1).max(0) as usize
            }
            Elements::List(elements) => elements.len(),
        }
    }

    pub fn get(&self, index: usize) -> Value {
        match self {
            Elements::Interval(low, _) => Value::Int(low + index as i32),
            Elements::List(elements) => elements[index].clone(),
        }
    }
}

/// One variable of a list of bounds, with the elements it ranges over.
pub(super) struct Variable<'e> {
    pub binder: Binder<'e>,
    pub elements: Elements,
    /// The expression of the set, where a failure to bind an element of it is reported.
    pub set: &'e Expr,
}

impl Evaluator {
    /// The variables of `bounds`, with their sets evaluated in order.
    pub(super) fn variables<'e>(
        &self,
        bounds: &'e [Bound],
        env: &mut Env<'_>,
    ) -> Result<Vec<Variable<'e>>> {
        let mut variables = Vec::new();
        for bound in bounds {
            let set = self.eval(&bound.set, env)?;
            let elements = self.bound_elements(set, &bound.set, env)?;
            for binder in binders(&bound.pattern) {
                variables.push(Variable { binder, elements: elements.clone(), set: &bound.set });
            }
        }
        Ok(variables)
    }

    /// The elements of the set of a bound, which TLC must be able to enumerate.
    pub(super) fn bound_elements(
        &self,
        set: Value,
        expr: &Expr,
        env: &Env<'_>,
    ) -> Result<Elements> {
        if let Value::Interval(low, high) = set {
            set.cardinality().at(self, env, expr)?;
            return Ok(Elements::Interval(low, high));
        }
        if !set.is_set() || is_overridden(&set) {
            return Err(self.error(env, expr, non_enumerable(&set, &self.node(env, expr))));
        }
        Ok(Elements::List(set.elements().at(self, env, expr)?))
    }

    /// Binds the variables to each combination of their elements, the first variable varying
    /// fastest, until `visit` returns true. Returns whether it did.
    pub(super) fn for_each_binding<'a>(
        &self,
        variables: &[Variable<'_>],
        env: &mut Env<'a>,
        mut visit: impl FnMut(&mut Env<'a>, &[usize]) -> Result<bool>,
    ) -> Result<bool> {
        if variables.iter().any(|variable| variable.elements.len() == 0) {
            return Ok(false);
        }
        let mut indexes = vec![0; variables.len()];
        for variable in variables.iter().rev() {
            self.bind_at(variable, 0, env)?;
        }
        loop {
            if visit(env, &indexes)? {
                return Ok(true);
            }
            let mut position = 0;
            loop {
                let Some(variable) = variables.get(position) else { return Ok(false) };
                indexes[position] += 1;
                if indexes[position] < variable.elements.len() {
                    self.bind_at(variable, indexes[position], env)?;
                    break;
                }
                indexes[position] = 0;
                self.bind_at(variable, 0, env)?;
                position += 1;
            }
        }
    }

    fn bind_at(&self, variable: &Variable<'_>, index: usize, env: &mut Env<'_>) -> Result<()> {
        let result = bind(variable.binder, variable.elements.get(index), env);
        result.at(self, env, variable.set)
    }

    /// `\A` or `\E` over bounded sets.
    #[inline(never)]
    pub(super) fn quantifier(
        &self,
        quantifier: Quantifier,
        bounds: &[Bound],
        body: &Expr,
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let is_forall = match quantifier {
            Quantifier::Forall => true,
            Quantifier::Exists => false,
            Quantifier::TemporalForall | Quantifier::TemporalExists => {
                return self.fail_at(env, expr, TEMPORAL_ERROR);
            }
        };
        let description = if is_forall { "the body of \\A" } else { "the body of \\E" };
        let variables = self.variables(bounds, env)?;
        let is_decided =
            self.for_each_binding(&variables, env, |env, _| match self.eval(body, env)? {
                Value::Bool(value) => Ok(value != is_forall),
                value => Err(self.error(env, expr, expected_boolean(description, &value))),
            })?;
        Ok(Value::Bool(is_decided != is_forall))
    }

    /// `CHOOSE x \in S : body`: the first element of `S` in TLC's order that satisfies `body`.
    #[inline(never)]
    pub(super) fn choose(
        &self,
        pattern: &Pattern,
        set: Option<&Expr>,
        body: &Expr,
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let Some(set_expr) = set else {
            return self.fail_at(env, expr, "TLC cannot evaluate an unbounded CHOOSE");
        };
        let set = self.eval(set_expr, env)?;
        if !set.is_set() || is_overridden(&set) {
            let message = format!(
                "Attempted to compute the value of an expression of\nform CHOOSE x \\in S: P, but S was not enumerable.\n{}",
                self.range(env, expr)
            );
            return Err(self.error(env, expr, message));
        }
        let elements = self.bound_elements(set, set_expr, env)?;
        for index in 0..elements.len() {
            let element = elements.get(index);
            for binder in binders(pattern) {
                bind(binder, element.clone(), env).at(self, env, set_expr)?;
            }
            match self.eval(body, env)? {
                Value::Bool(true) => return Ok(element),
                Value::Bool(false) => {}
                value => {
                    return Err(self.error(
                        env,
                        expr,
                        expected_boolean("the body of CHOOSE", &value),
                    ));
                }
            }
        }
        let message = format!(
            "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\n{}",
            self.range(env, expr)
        );
        Err(self.error(env, expr, message))
    }

    /// `{x \in S : pred}`. TLC filters a set enumeration or an interval at once, and any other
    /// set lazily, failing only when it uses the result.
    #[inline(never)]
    pub(super) fn set_filter(
        &self,
        bound: &Bound,
        pred: &Expr,
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let base = self.eval(&bound.set, env)?;
        if !matches!(base, Value::Set(_) | Value::MixedSet(_) | Value::Interval(..)) {
            let test = self.filter_test(expr, env);
            return Ok(Value::lazy(LazySet::Filtered { base, test }));
        }
        let mut kept = Vec::new();
        for element in base.elements().at(self, env, expr)?.iter() {
            for binder in binders(&bound.pattern) {
                bind(binder, element.clone(), env).at(self, env, &bound.set)?;
            }
            match self.eval(pred, env)? {
                Value::Bool(true) => kept.push(element.clone()),
                Value::Bool(false) => {}
                value => {
                    let message = expected_boolean("a set filter predicate", &value);
                    return Err(self.error(env, expr, message));
                }
            }
        }
        Ok(Value::Set(kept.into()))
    }

    /// The test of a lazily filtered set, which evaluates the predicate of `filter` where the
    /// set was built.
    fn filter_test(&self, filter: &Expr, env: &Env<'_>) -> Predicate {
        let evaluator = self.clone();
        let captured = env.capture();
        // SAFETY: every expression this evaluator evaluates is part of its spec.
        let filter = unsafe { SpecRef::new(&self.spec, filter) };
        Arc::new(move |element| {
            let ExprKind::SetFilter { bound, pred } = &filter.get().kind else {
                unreachable!("a filter test is built from a set filter")
            };
            let mut env = captured.env();
            for binder in binders(&bound.pattern) {
                bind(binder, element.clone(), &mut env)?;
            }
            match evaluator.eval(pred, &mut env) {
                Ok(Value::Bool(value)) => Ok(value),
                Ok(value) => Err(Error(expected_boolean("a set filter predicate", &value))),
                Err(error) => Err(Error(error.message)),
            }
        })
    }

    /// `{body : x \in S, ...}`.
    #[inline(never)]
    pub(super) fn set_map(
        &self,
        bounds: &[Bound],
        body: &Expr,
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let variables = self.variables(bounds, env)?;
        let mut elements = Vec::new();
        self.for_each_binding(&variables, env, |env, _| {
            elements.push(self.eval(body, env)?);
            Ok(false)
        })?;
        Value::set(elements).at(self, env, expr)
    }
}

fn expected_boolean(description: &str, value: &Value) -> String {
    format!("Expected {description} to be a boolean but found {value}")
}

/// TLC's error for a quantifier bound it can't enumerate, which SANY describes as `node`.
fn non_enumerable(set: &Value, node: &str) -> String {
    let text = set.to_string();
    let quantified = format!(
        "universally (\\A) or existentially (\\E) quantify over {text}, because this would require checking an\ninfinite number of cases."
    );
    let explanation = match set {
        Value::Lazy(lazy) => match **lazy {
            LazySet::Seq(_) => Some(format!(
                "In TLA+, Seq(S) represents the set of all finite sequences whose elements come from the set S. Even when S\nis a finite set, the number of possible sequences in Seq(S) is unbounded because sequences can have any\nfinite length (e.g., length 0, 1, 2, and so on). As a result, TLC cannot evaluate expressions that\n{quantified} Note that for a finite set of sequences s, TLC handles s \\subseteq Seq(S).\nSee https://explain.tlapl.us/seq-unenumerable for additional details."
            )),
            LazySet::Nat | LazySet::Int => Some(format!(
                "The set {text} contains infinitely many elements. As a result, TLC cannot evaluate expressions that\n{quantified} Note that TLC handles set membership like T \\subseteq {text} for any finite set T."
            )),
            _ => None,
        },
        _ => None,
    };
    match explanation {
        Some(explanation) => format!(
            "TLC encountered the non-enumerable quantifier bound\n{text}\n{node}\n{explanation}"
        ),
        None => format!("TLC encountered a non-enumerable quantifier bound\n{text}.\n{node}"),
    }
}
