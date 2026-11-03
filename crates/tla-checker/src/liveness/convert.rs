//! The translation of temporal formulas into liveness formulas, ported from tla-ts
//! `toLiveExpression`, TLC's `Liveness.astToLive`: TLC expands the definitions a temporal
//! formula applies, with the values of their arguments, unrolls quantifiers over constant sets,
//! decides `IF`s with constant conditions, and takes each part below temporal level as one
//! formula it evaluates in the frames of the calls it expanded.

use std::collections::HashMap;
use std::rc::Rc;

use tla_ast::{Fairness, Quantifier, Span};
use tla_eval::{Evaluator, Frames, Value};
use tla_resolve::{Builtin, DefBody, DefId, Expr, ExprKind, Level, Pattern};

use super::live::{Atom, AtomKind, Eval, Live};
use crate::level::Levels;
use crate::plan::describe_range;

/// How deep TLC expands definitions in a temporal formula before it reports a stack overflow.
const MAXIMUM_EXPANSION_DEPTH: usize = 100;

const STACK_OVERFLOW: &str = "Stack overflow while processing the specification.";

/// What the translation of a part found: a formula, or why TLC can't translate it.
enum Failure {
    /// An error TLC reports as it translates, which an enclosing formula below temporal level
    /// may still take whole.
    Eval(String),
    /// An error that stops the translation.
    Fatal(String),
}

type Translated = Result<Live, Failure>;

/// Where an expression is: the frames of the definition whose body holds it, and how high the
/// arguments of the calls into those frames are.
#[derive(Clone)]
struct Place {
    frames: Frames,
    def: DefId,
    arguments: Level,
}

pub struct Translation<'e> {
    evaluator: &'e Evaluator,
    overrides: &'e HashMap<DefId, DefId>,
    enabled: &'e HashMap<(DefId, Span), DefId>,
    /// The spec's next-state relation.
    next: Option<DefId>,
    levels: Levels,
    /// The expressions the atoms evaluate, by index.
    pub exprs: Vec<&'e Expr>,
    atoms: usize,
    state_atoms: usize,
    depth: usize,
}

impl<'e> Translation<'e> {
    pub fn new(
        evaluator: &'e Evaluator,
        overrides: &'e HashMap<DefId, DefId>,
        enabled: &'e HashMap<(DefId, Span), DefId>,
        next: Option<DefId>,
    ) -> Self {
        Self {
            evaluator,
            overrides,
            enabled,
            next,
            levels: Levels::tlc(),
            exprs: Vec::new(),
            atoms: 0,
            state_atoms: 0,
            depth: 0,
        }
    }

    /// The formula of the module-level definition `def`, a temporal part of the spec.
    pub fn formula(&mut self, def: DefId) -> Result<Live, String> {
        let spec = self.evaluator.spec();
        let DefBody::Expr(body) = &spec.def(def).body else {
            return Err("A temporal formula must be an expression.".into());
        };
        let place =
            Place { frames: self.evaluator.module_frames(def), def, arguments: Level::Constant };
        match self.convert(body, &place) {
            Ok(live) => Ok(live),
            Err(Failure::Eval(message) | Failure::Fatal(message)) => Err(message),
        }
    }

    fn level(&self, expr: &Expr, place: &Place) -> Level {
        self.levels.level(self.evaluator.spec(), expr).max(place.arguments)
    }

    fn cannot_handle(&self, expr: &Expr, place: &Place, inner: Option<String>) -> Failure {
        let range = describe_range(self.evaluator.spec(), place.frames.module(), expr.span);
        let inner = inner.map(|inner| format!(":\n{inner}")).unwrap_or_default();
        Failure::Fatal(format!("TLC cannot handle the temporal formula {range}{inner}"))
    }

    fn eval(&self, expr: &'e Expr, place: &Place) -> Result<Value, Failure> {
        // SAFETY: `expr` is an expression of the evaluator's spec, in the body of `place.def`.
        unsafe { self.evaluator.eval_in(&place.frames, expr, None, None) }
            .map_err(|error| Failure::Eval(error.to_string()))
    }

    fn atom(&mut self, kind: AtomKind) -> Rc<Atom> {
        self.atoms += 1;
        let slot = self.state_atoms;
        if !matches!(kind, AtomKind::Action { .. }) {
            self.state_atoms += 1;
        }
        Rc::new(Atom { id: self.atoms, slot, kind })
    }

    /// The number of state predicates among the atoms.
    pub fn state_atoms(&self) -> usize {
        self.state_atoms
    }

    fn evaluated(&mut self, expr: &'e Expr, place: &Place) -> Eval {
        self.exprs.push(expr);
        Eval { frames: place.frames.clone(), expr: self.exprs.len() - 1 }
    }

    /// `expr` as one formula at `level`: TLC evaluates a constant one now.
    fn atom_of(&mut self, expr: &'e Expr, place: &Place, level: Level) -> Translated {
        // TLC after 1.7.4 bounds the level of a formula whose parts are constant by its own.
        let level = if level == Level::Constant { self.level(expr, place) } else { level };
        match level {
            Level::Constant => match self.eval(expr, place)?.as_bool() {
                Some(value) => Ok(Live::Bool(value)),
                None => {
                    let range =
                        describe_range(self.evaluator.spec(), place.frames.module(), expr.span);
                    Err(Failure::Eval(format!(
                        "TLC expected a boolean value, but did not find one. {range}"
                    )))
                }
            },
            Level::State => {
                let eval = self.evaluated(expr, place);
                Ok(Live::Atom(self.atom(AtomKind::State(eval))))
            }
            _ => {
                let action = self.evaluated(expr, place);
                Ok(Live::Atom(self.atom(AtomKind::Action {
                    action,
                    unchanged: None,
                    enabled: None,
                    is_next: false,
                })))
            }
        }
    }

    /// `parts` translated from `expr`, or `expr` whole if they are below temporal level.
    fn whole_of(&mut self, expr: &'e Expr, place: &Place, parts: Live) -> Translated {
        let level = parts.level();
        if level > Level::Action { Ok(parts) } else { self.atom_of(expr, place, level) }
    }

    fn convert(&mut self, expr: &'e Expr, place: &Place) -> Translated {
        let level = self.level(expr, place);
        if level <= Level::Action && !is_translated_whole(expr) {
            return self.atom_of(expr, place, level);
        }
        match &expr.kind {
            ExprKind::Builtin { op, args } => match op {
                Builtin::Always => Ok(Live::always(self.convert(&args[0], place)?)),
                Builtin::Eventually => Ok(Live::eventually(self.convert(&args[0], place)?)),
                Builtin::LeadsTo => {
                    let from = self.convert(&args[0], place)?;
                    let to = self.convert(&args[1], place)?;
                    Ok(Live::always(Live::or(vec![Live::not(from), Live::eventually(to)])))
                }
                Builtin::Not => {
                    let parts = Live::not(self.convert(&args[0], place)?);
                    self.whole_of(expr, place, parts)
                }
                Builtin::Implies => {
                    let from = self.convert(&args[0], place)?;
                    let to = self.convert(&args[1], place)?;
                    self.whole_of(expr, place, Live::or(vec![Live::not(from), to]))
                }
                _ => Err(self.cannot_handle(expr, place, None)),
            },
            ExprKind::And(items) | ExprKind::Or(items) => {
                let parts = items
                    .iter()
                    .map(|item| self.convert(item, place))
                    .collect::<Result<Vec<_>, _>>()?;
                let junction = match &expr.kind {
                    ExprKind::And(_) => Live::and(parts),
                    _ => Live::or(parts),
                };
                self.whole_of(expr, place, junction)
            }
            ExprKind::If { cond, then, otherwise } => {
                if self.level(cond, place) == Level::Constant
                    && let Some(value) = self.eval(cond, place)?.as_bool()
                {
                    return self.convert(if value { then } else { otherwise }, place);
                }
                let condition = self.convert(cond, place)?;
                let then = self.convert(then, place)?;
                let otherwise = self.convert(otherwise, place)?;
                let parts = Live::or(vec![
                    Live::and(vec![condition.clone(), then]),
                    Live::and(vec![Live::not(condition), otherwise]),
                ]);
                self.whole_of(expr, place, parts)
            }
            ExprKind::Quant { quantifier, bounds, body } => {
                let forall = matches!(quantifier, Quantifier::Forall);
                let is_constant =
                    bounds.iter().all(|bound| self.level(&bound.set, place) == Level::Constant);
                if !is_constant {
                    if level <= Level::Action {
                        return self.atom_of(expr, place, level);
                    }
                    return Err(self.cannot_handle(expr, place, None));
                }
                let mut operands = Vec::new();
                let unrolled = self.unroll(bounds, place, &mut |translation, bound| {
                    operands.push(translation.convert(body, bound)?);
                    Ok(())
                });
                match unrolled {
                    Ok(()) => {}
                    Err(Failure::Eval(message)) => {
                        if level <= Level::Action {
                            return self.atom_of(expr, place, level);
                        }
                        let inner = forall.then_some(message);
                        return Err(self.cannot_handle(expr, place, inner));
                    }
                    Err(fatal) => return Err(fatal),
                }
                if operands.is_empty() {
                    return Ok(Live::Bool(forall));
                }
                let junction = if forall { Live::and(operands) } else { Live::or(operands) };
                self.whole_of(expr, place, junction)
            }
            ExprKind::Fairness { fairness, action, sub } => {
                let Some(&enabled) = self.enabled.get(&(place.def, expr.span)) else {
                    return Err(self.cannot_handle(expr, place, None));
                };
                let spec = self.evaluator.spec();
                let DefBody::Expr(enabled) = &spec.def(enabled).body else {
                    return Err(self.cannot_handle(expr, place, None));
                };
                let enabled = self.evaluated(enabled, place);
                let enabled = self.atom(AtomKind::Enabled(enabled));
                let disabled = Live::not(Live::Atom(enabled.clone()));
                let is_next = match &action.kind {
                    ExprKind::Call { def, scope: tla_resolve::Scope::Global, args } => {
                        args.is_empty()
                            && Some(*self.overrides.get(def).unwrap_or(def)) == self.next
                    }
                    _ => false,
                };
                let taken = AtomKind::Action {
                    action: self.evaluated(action, place),
                    unchanged: Some(self.evaluated(sub, place)),
                    enabled: Some(enabled),
                    is_next,
                };
                let taken = Live::Atom(self.atom(taken));
                Ok(match fairness {
                    Fairness::Weak => {
                        Live::always(Live::eventually(Live::or(vec![disabled, taken])))
                    }
                    Fairness::Strong => Live::or(vec![
                        Live::eventually(Live::always(disabled)),
                        Live::always(Live::eventually(taken)),
                    ]),
                })
            }
            ExprKind::Call { def, scope, args } => {
                self.convert_call(expr, place, *def, scope, args)
            }
            _ => Err(self.cannot_handle(expr, place, None)),
        }
    }

    /// The body of the definition a call applies, translated with the call's arguments.
    fn convert_call(
        &mut self,
        expr: &'e Expr,
        place: &Place,
        def: DefId,
        scope: &'e tla_resolve::Scope,
        args: &'e [Expr],
    ) -> Translated {
        let spec = self.evaluator.spec();
        let target = *self.overrides.get(&def).unwrap_or(&def);
        let DefBody::Expr(body) = &spec.def(target).body else {
            return Err(self.cannot_handle(expr, place, None));
        };
        if self.depth >= MAXIMUM_EXPANSION_DEPTH {
            return Err(Failure::Fatal(STACK_OVERFLOW.into()));
        }
        let mut arguments =
            args.iter().map(|arg| self.level(arg, place)).fold(place.arguments, Level::max);
        let mut instance = scope;
        while let tla_resolve::Scope::Instance { parent, args } = instance {
            arguments = args.iter().map(|arg| self.level(arg, place)).fold(arguments, Level::max);
            instance = parent;
        }
        // SAFETY: the arguments and the scope are the spec's, written in `place`.
        let frames = unsafe { self.evaluator.call_frames(&place.frames, target, scope, args) }
            .map_err(|error| Failure::Eval(error.to_string()))?;
        let inner = Place { frames, def: target, arguments };
        self.depth += 1;
        let translated = self.convert(body, &inner);
        self.depth -= 1;
        match translated {
            Ok(result) => {
                let level = result.level();
                if level > Level::Action { Ok(result) } else { self.atom_of(expr, place, level) }
            }
            // TLC takes an application whose expansion fails for a formula it can't handle,
            // and after 1.7.4 fails as the expansion of a recursive operator does.
            Err(Failure::Fatal(message)) if message == STACK_OVERFLOW => {
                Err(Failure::Fatal(message))
            }
            Err(failure) if self.is_recursive(target) => Err(failure),
            Err(_) => Err(self.cannot_handle(expr, place, None)),
        }
    }

    fn is_recursive(&self, def: DefId) -> bool {
        let spec = self.evaluator.spec();
        let DefBody::Expr(body) = &spec.def(def).body else { return false };
        let mut found = false;
        crate::level::visit(body, &mut |expr| {
            if let ExprKind::Call { def: called, .. } = &expr.kind {
                found |= *called == def;
            }
        });
        found
    }

    /// Calls `each` with `place` binding each element of the sets of `bounds`, the first
    /// bound's varying slowest.
    fn unroll(
        &mut self,
        bounds: &'e [tla_resolve::Bound],
        place: &Place,
        each: &mut dyn FnMut(&mut Self, &Place) -> Result<(), Failure>,
    ) -> Result<(), Failure> {
        let Some((bound, rest)) = bounds.split_first() else { return each(self, place) };
        let set = self.eval(&bound.set, place)?;
        let elements = set.elements().map_err(|error| Failure::Eval(error.to_string()))?;
        let bindings: Vec<Vec<(usize, Value)>> = match &bound.pattern {
            Pattern::Names(slots) => {
                let mut bindings = vec![Vec::new()];
                for &slot in slots {
                    bindings = bindings
                        .into_iter()
                        .flat_map(|binding| {
                            elements.iter().map(move |element| {
                                let mut extended = binding.clone();
                                extended.push((slot, element.clone()));
                                extended
                            })
                        })
                        .collect();
                }
                bindings
            }
            Pattern::Tuple(slots) => elements
                .iter()
                .map(|element| match element {
                    Value::Tuple(items) if items.len() == slots.len() => {
                        Ok(slots.iter().copied().zip(items.iter().cloned()).collect())
                    }
                    _ => Err(Failure::Eval(format!("A tuple pattern can't bind {element}."))),
                })
                .collect::<Result<_, _>>()?,
        };
        for binding in bindings {
            let mut frames = place.frames.clone();
            for (slot, value) in binding {
                frames = self.evaluator.bind(&frames, slot, value);
            }
            let bound = Place { frames, ..place.clone() };
            self.unroll(rest, &bound, each)?;
        }
        Ok(())
    }
}

/// The formulas below temporal level whose parts TLC translates, as a constant part, such as a
/// quantifier over the empty set, can make the formula constant.
fn is_translated_whole(expr: &Expr) -> bool {
    matches!(
        &expr.kind,
        ExprKind::And(_)
            | ExprKind::Or(_)
            | ExprKind::Quant { quantifier: Quantifier::Forall | Quantifier::Exists, .. }
            | ExprKind::If { .. }
            | ExprKind::Builtin { op: Builtin::Not | Builtin::Implies, .. }
    )
}
