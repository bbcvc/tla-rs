//! A liveness formula as spec processing builds it, before the model checker can evaluate
//! anything: the parts below temporal level are definitions, and what depends on values, the
//! quantifiers over constant sets that TLC unrolls, the conditions of `IF`s it decides, and the
//! parts that are constants, is left to [`Instantiator`], as tla-ts `toLiveExpression` does it.

use std::rc::Rc;

use tla_eval::{Evaluator, Value};
use tla_resolve::{DefId, Pattern};

use super::live::{Atom, AtomKind, Eval, Live};

#[derive(Clone, Debug)]
pub enum Template {
    Bool(bool),
    /// A constant formula, which must be `TRUE` or `FALSE`.
    Constant(DefId),
    State(DefId),
    Action(DefId),
    /// `WF_v(A)` or `SF_v(A)`, with `ENABLED <<A>>_v`, `A`, and `UNCHANGED v`.
    Fairness {
        strong: bool,
        enabled: DefId,
        action: DefId,
        unchanged: DefId,
    },
    Not(Box<Template>),
    Always(Box<Template>),
    Eventually(Box<Template>),
    And(Vec<Template>),
    Or(Vec<Template>),
    /// `\A` or `\E` over constant sets, whose bound variables are slots of the frame of the
    /// definitions in `body`.
    Quantifier {
        forall: bool,
        bounds: Vec<(DefId, Pattern)>,
        body: Box<Template>,
    },
    /// `IF` with a constant condition.
    If {
        condition: DefId,
        then: Box<Template>,
        otherwise: Box<Template>,
    },
}

/// Turns templates into formulas with the evaluator, binding the variables of the quantifiers
/// it unrolls.
pub struct Instantiator<'a> {
    evaluator: &'a Evaluator,
    atoms: usize,
}

type Bound = Rc<[(usize, Value)]>;

/// What [`Instantiator::unroll`] calls with each binding.
type Each<'e, 'a> =
    dyn FnMut(&mut Instantiator<'a>, Vec<(usize, Value)>) -> Result<(), String> + 'e;

impl<'a> Instantiator<'a> {
    pub fn new(evaluator: &'a Evaluator) -> Self {
        Self { evaluator, atoms: 0 }
    }

    pub fn formula(&mut self, template: &Template) -> Result<Live, String> {
        self.instantiate(template, &Rc::from([]))
    }

    fn atom(&mut self, kind: AtomKind) -> Rc<Atom> {
        self.atoms += 1;
        Rc::new(Atom { id: self.atoms, kind })
    }

    fn eval(def: DefId, bound: &Bound) -> Eval {
        Eval { def, bound: bound.clone() }
    }

    fn constant(&self, def: DefId, bound: &Bound) -> Result<Value, String> {
        self.evaluator.eval_bound(def, bound, None, None).map_err(|error| error.to_string())
    }

    fn boolean(&self, def: DefId, bound: &Bound) -> Result<bool, String> {
        let value = self.constant(def, bound)?;
        value.as_bool().ok_or_else(|| {
            format!("TLC expected a boolean value, but did not find one. The value was {value}")
        })
    }

    fn instantiate(&mut self, template: &Template, bound: &Bound) -> Result<Live, String> {
        Ok(match template {
            Template::Bool(value) => Live::Bool(*value),
            Template::Constant(def) => Live::Bool(self.boolean(*def, bound)?),
            Template::State(def) => Live::Atom(self.atom(AtomKind::State(Self::eval(*def, bound)))),
            Template::Action(def) => Live::Atom(self.atom(AtomKind::Action {
                action: Self::eval(*def, bound),
                unchanged: None,
                enabled: None,
            })),
            Template::Fairness { strong, enabled, action, unchanged } => {
                let enabled = self.atom(AtomKind::Enabled(Self::eval(*enabled, bound)));
                let disabled = Live::not(Live::Atom(enabled.clone()));
                let taken = Live::Atom(self.atom(AtomKind::Action {
                    action: Self::eval(*action, bound),
                    unchanged: Some(Self::eval(*unchanged, bound)),
                    enabled: Some(enabled),
                }));
                if *strong {
                    Live::or(vec![
                        Live::eventually(Live::always(disabled)),
                        Live::always(Live::eventually(taken)),
                    ])
                } else {
                    Live::always(Live::eventually(Live::or(vec![disabled, taken])))
                }
            }
            Template::Not(body) => Live::not(self.instantiate(body, bound)?),
            Template::Always(body) => Live::always(self.instantiate(body, bound)?),
            Template::Eventually(body) => Live::eventually(self.instantiate(body, bound)?),
            Template::And(operands) => Live::and(self.all(operands, bound)?),
            Template::Or(operands) => Live::or(self.all(operands, bound)?),
            Template::If { condition, then, otherwise } => {
                let branch = if self.boolean(*condition, bound)? { then } else { otherwise };
                self.instantiate(branch, bound)?
            }
            Template::Quantifier { forall, bounds, body } => {
                let mut operands = Vec::new();
                self.unroll(bounds, bound.to_vec(), &mut |instantiator, bound| {
                    operands.push(instantiator.instantiate(body, &Rc::from(bound))?);
                    Ok(())
                })?;
                match (operands.is_empty(), forall) {
                    (true, _) => Live::Bool(*forall),
                    (false, true) => Live::and(operands),
                    (false, false) => Live::or(operands),
                }
            }
        })
    }

    fn all(&mut self, operands: &[Template], bound: &Bound) -> Result<Vec<Live>, String> {
        operands.iter().map(|operand| self.instantiate(operand, bound)).collect()
    }

    /// Calls `each` with every binding of the variables of `bounds`, the first bound's
    /// varying slowest, in TLC's order of each set.
    fn unroll(
        &mut self,
        bounds: &[(DefId, Pattern)],
        bound: Vec<(usize, Value)>,
        each: &mut Each<'_, 'a>,
    ) -> Result<(), String> {
        let Some(((set, pattern), rest)) = bounds.split_first() else {
            return each(self, bound);
        };
        let set = self.constant(*set, &Rc::from(bound.clone()))?;
        let elements = set.elements().map_err(|error| error.to_string())?;
        match pattern {
            Pattern::Names(slots) => {
                self.names(slots, &elements, bound, &mut |instantiator, bound| {
                    instantiator.unroll(rest, bound, each)
                })
            }
            Pattern::Tuple(slots) => {
                for element in elements.iter() {
                    let Value::Tuple(items) = element else {
                        return Err(format!("A tuple pattern can't bind {element}."));
                    };
                    if items.len() != slots.len() {
                        return Err(format!("A tuple pattern can't bind {element}."));
                    }
                    let mut extended = bound.clone();
                    extended.extend(slots.iter().copied().zip(items.iter().cloned()));
                    self.unroll(rest, extended, each)?;
                }
                Ok(())
            }
        }
    }

    /// Each binding of `slots` to elements of a set, the first slot varying slowest.
    fn names(
        &mut self,
        slots: &[usize],
        elements: &[Value],
        bound: Vec<(usize, Value)>,
        each: &mut Each<'_, 'a>,
    ) -> Result<(), String> {
        let Some((slot, rest)) = slots.split_first() else {
            return each(self, bound);
        };
        for element in elements {
            let mut extended = bound.clone();
            extended.push((*slot, element.clone()));
            self.names(rest, elements, extended, each)?;
        }
        Ok(())
    }
}
