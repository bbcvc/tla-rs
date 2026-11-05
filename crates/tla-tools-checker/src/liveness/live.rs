//! TLC's liveness formulas (`LiveExprNode`), and their normal forms, ported from tla-ts
//! `tableau.ts`.

use std::rc::Rc;

use tla_tools_eval::Frames;
use tla_tools_resolve::Level;

/// What evaluates a part of a liveness formula: an expression of the spec, by its index among
/// those the translation kept, in the frames of the calls the translation expanded, with the
/// variables of the quantifiers it unrolled bound.
#[derive(Clone)]
pub struct Eval {
    pub frames: Frames,
    pub expr: usize,
}

impl std::fmt::Debug for Eval {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "Eval({})", self.expr)
    }
}

/// A part of a formula below temporal level, which the model checker evaluates.
#[derive(Debug)]
pub struct Atom {
    /// Atoms are equal only to themselves.
    pub id: usize,
    /// The place of a state predicate's results among those of the others.
    pub slot: usize,
    pub kind: AtomKind,
}

#[derive(Debug)]
pub enum AtomKind {
    /// A state predicate.
    State(Eval),
    /// `ENABLED <<A>>_v` of a fairness condition.
    Enabled(Eval),
    /// An action. One a fairness condition takes is `<<A>>_v`: `A` on a step that changes the
    /// subscript `v`, which can't hold where the condition's `ENABLED` doesn't.
    ///
    /// When the action is the spec's next-state relation, every step of the behavior graph
    /// but a stuttering one satisfies it, since the search found it as a successor, and it
    /// isn't evaluated.
    Action { action: Eval, unchanged: Option<Eval>, enabled: Option<Rc<Atom>>, is_next: bool },
}

/// A liveness formula.
#[derive(Clone, Debug)]
pub enum Live {
    Bool(bool),
    Atom(Rc<Atom>),
    Not(Rc<Live>),
    Always(Rc<Live>),
    Eventually(Rc<Live>),
    /// The formula in the next state.
    Next(Rc<Live>),
    And(Rc<[Live]>),
    Or(Rc<[Live]>),
}

/// The largest disjunctive normal form TLC builds.
pub(super) const MAXIMUM_DISJUNCTS: u64 = 2_147_483_647;

impl Live {
    pub fn not(body: Live) -> Live {
        Live::Not(Rc::new(body))
    }

    pub fn always(body: Live) -> Live {
        Live::Always(Rc::new(body))
    }

    pub fn eventually(body: Live) -> Live {
        Live::Eventually(Rc::new(body))
    }

    pub(super) fn next(body: Live) -> Live {
        Live::Next(Rc::new(body))
    }

    /// A conjunction, with conjunctions among `operands` flattened into it.
    pub fn and(operands: Vec<Live>) -> Live {
        Live::And(flatten(operands, true).into())
    }

    /// A disjunction, with disjunctions among `operands` flattened into it.
    pub fn or(operands: Vec<Live>) -> Live {
        Live::Or(flatten(operands, false).into())
    }

    pub(super) fn pair(is_and: bool, left: Live, right: Live) -> Live {
        let operands: Rc<[Live]> = vec![left, right].into();
        if is_and { Live::And(operands) } else { Live::Or(operands) }
    }

    pub(super) fn junction(is_and: bool, operands: Vec<Live>) -> Live {
        if is_and { Live::and(operands) } else { Live::or(operands) }
    }

    pub(super) fn body(&self) -> Option<&Live> {
        match self {
            Live::Not(body) | Live::Always(body) | Live::Eventually(body) | Live::Next(body) => {
                Some(body)
            }
            _ => None,
        }
    }

    pub(super) fn operands(&self) -> Option<&[Live]> {
        match self {
            Live::And(operands) | Live::Or(operands) => Some(operands),
            _ => None,
        }
    }

    pub(super) fn is_atom(&self) -> bool {
        matches!(self, Live::Atom(_))
    }

    pub(super) fn is_state_atom(&self) -> bool {
        match self {
            Live::Bool(_) => true,
            Live::Atom(atom) => !matches!(atom.kind, AtomKind::Action { .. }),
            _ => false,
        }
    }

    /// The level of the formula.
    pub fn level(&self) -> Level {
        match self {
            Live::Bool(_) => Level::Constant,
            Live::Atom(atom) => match atom.kind {
                AtomKind::Action { .. } => Level::Action,
                _ => Level::State,
            },
            Live::Next(_) => Level::Action,
            Live::Not(body) => body.level(),
            Live::Always(_) | Live::Eventually(_) => Level::Temporal,
            Live::And(operands) | Live::Or(operands) => {
                operands.iter().map(Live::level).fold(Level::Constant, Level::max)
            }
        }
    }

    pub(super) fn contains_action(&self) -> bool {
        match self {
            Live::Atom(atom) => matches!(atom.kind, AtomKind::Action { .. }),
            Live::Bool(_) => false,
            Live::Not(body) | Live::Always(body) | Live::Eventually(body) | Live::Next(body) => {
                body.contains_action()
            }
            Live::And(operands) | Live::Or(operands) => operands.iter().any(Live::contains_action),
        }
    }

    pub fn contains_always(&self) -> bool {
        match self {
            Live::Always(_) => true,
            Live::Eventually(body) | Live::Not(body) | Live::Next(body) => body.contains_always(),
            Live::And(operands) | Live::Or(operands) => operands.iter().any(Live::contains_always),
            _ => false,
        }
    }

    /// The structure of the formula, in which each atom stands for itself, so that equal terms
    /// share a key.
    pub fn key(&self) -> String {
        match self {
            Live::Bool(value) => value.to_string(),
            Live::Atom(atom) => format!("#{}", atom.id),
            Live::Not(body) => format!("Not({})", body.key()),
            Live::Always(body) => format!("Always({})", body.key()),
            Live::Eventually(body) => format!("Eventually({})", body.key()),
            Live::Next(body) => format!("Next({})", body.key()),
            Live::And(operands) => format!("And({})", keys(operands)),
            Live::Or(operands) => format!("Or({})", keys(operands)),
        }
    }
}

fn keys(operands: &[Live]) -> String {
    operands.iter().map(Live::key).collect::<Vec<_>>().join(",")
}

fn flatten(operands: Vec<Live>, is_and: bool) -> Vec<Live> {
    let mut flat = Vec::with_capacity(operands.len());
    for operand in operands {
        match (&operand, is_and) {
            (Live::And(inner), true) | (Live::Or(inner), false) => {
                flat.extend(flatten(inner.to_vec(), is_and));
            }
            _ => flat.push(operand),
        }
    }
    flat
}

pub(super) fn is_equal(left: &Live, right: &Live) -> bool {
    left.key() == right.key()
}

pub(super) fn is_member(items: &[Live], term: &Live) -> bool {
    let key = term.key();
    items.iter().any(|item| item.key() == key)
}

pub(super) fn push_negation(term: &Live, is_negated: bool) -> Live {
    match term {
        Live::Bool(value) => Live::Bool(*value != is_negated),
        Live::Atom(_) | Live::Next(_) => {
            if is_negated {
                Live::not(term.clone())
            } else {
                term.clone()
            }
        }
        Live::Not(body) => push_negation(body, !is_negated),
        Live::And(operands) | Live::Or(operands) => {
            let is_and = matches!(term, Live::And(_)) != is_negated;
            let operands = operands.iter().map(|operand| push_negation(operand, is_negated));
            Live::junction(is_and, operands.collect())
        }
        Live::Always(body) | Live::Eventually(body) => {
            let body = push_negation(body, is_negated);
            if is_negated == matches!(term, Live::Always(_)) {
                Live::eventually(body)
            } else {
                Live::always(body)
            }
        }
    }
}

pub(super) fn negate(term: &Live) -> Live {
    match term {
        Live::Bool(value) => Live::Bool(!value),
        Live::Not(body) => (**body).clone(),
        Live::And(operands) => Live::or(operands.iter().map(negate).collect()),
        Live::Or(operands) => Live::and(operands.iter().map(negate).collect()),
        Live::Always(body) => Live::eventually(negate(body)),
        Live::Eventually(body) => Live::always(negate(body)),
        _ => Live::not(term.clone()),
    }
}

pub(super) fn simplify(term: &Live) -> Live {
    match term {
        Live::And(operands) | Live::Or(operands) => {
            let absorbing = matches!(term, Live::Or(_));
            let mut kept = Vec::new();
            for operand in operands.iter() {
                match simplify(operand) {
                    Live::Bool(value) if value == absorbing => return Live::Bool(absorbing),
                    Live::Bool(_) => {}
                    simplified => kept.push(simplified),
                }
            }
            match kept.len() {
                0 => Live::Bool(!absorbing),
                1 => kept.pop().unwrap(),
                _ => Live::junction(!absorbing, kept),
            }
        }
        Live::Not(body) => match simplify(body) {
            Live::Bool(value) => Live::Bool(!value),
            body => Live::not(body),
        },
        Live::Always(body) => match simplify(body) {
            Live::Always(inner) => Live::always((*inner).clone()),
            body => Live::always(body),
        },
        Live::Eventually(body) => match simplify(body) {
            Live::Eventually(inner) => Live::eventually((*inner).clone()),
            body => Live::eventually(body),
        },
        _ => term.clone(),
    }
}

/// `P` of `[]<>P`.
pub(super) fn infinitely_often_body(term: &Live) -> Option<&Live> {
    match term {
        Live::Always(body) => match &**body {
            Live::Eventually(inner) => Some(inner),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn disjunctive_normal_form(term: &Live) -> Result<Live, String> {
    match term {
        Live::And(operands) => {
            let mut items = Vec::new();
            let mut total: u64 = 1;
            for operand in operands.iter() {
                let normal = disjunctive_normal_form(operand)?;
                match &normal {
                    Live::And(inner) => {
                        items.extend(inner.iter().cloned());
                        continue;
                    }
                    Live::Or(inner) => {
                        total = total.saturating_mul(inner.len() as u64);
                        if total > MAXIMUM_DISJUNCTS {
                            return Err("TLC cannot handle the temporal formula because it exceeds the maximum supported size in disjunctive normal form.".into());
                        }
                    }
                    _ => {}
                }
                items.push(normal);
            }
            if total == 1 {
                return Ok(Live::And(items.into()));
            }
            let total = total as usize;
            let mut conjunctions: Vec<Vec<Live>> = vec![Vec::new(); total];
            let (mut groups, mut repeat) = (1, total);
            for item in &items {
                let Live::Or(choices) = item else {
                    for conjunction in &mut conjunctions {
                        conjunction.push(item.clone());
                    }
                    continue;
                };
                repeat /= choices.len();
                let mut position = 0;
                for _ in 0..groups {
                    for choice in choices.iter() {
                        for _ in 0..repeat {
                            conjunctions[position].push(choice.clone());
                            position += 1;
                        }
                    }
                }
                groups *= choices.len();
            }
            Ok(Live::Or(conjunctions.into_iter().map(Live::and).collect::<Vec<_>>().into()))
        }
        Live::Or(operands) => {
            let mut infinitely_often = Vec::new();
            let mut disjuncts = Vec::new();
            for operand in operands.iter() {
                let normal = disjunctive_normal_form(operand)?;
                let items = match &normal {
                    Live::Or(inner) => inner.to_vec(),
                    _ => vec![normal],
                };
                for item in items {
                    match infinitely_often_body(&item) {
                        Some(body) => infinitely_often.push(body.clone()),
                        None => disjuncts.push(item),
                    }
                }
            }
            if !infinitely_often.is_empty() {
                let body = if infinitely_often.len() == 1 {
                    infinitely_often.pop().unwrap()
                } else {
                    Live::or(infinitely_often)
                };
                disjuncts.push(Live::always(Live::eventually(body)));
            }
            Ok(Live::or(disjuncts))
        }
        Live::Not(body) if body.is_atom() => Ok(term.clone()),
        Live::Not(body) => disjunctive_normal_form(&negate(body)),
        _ => Ok(term.clone()),
    }
}

pub(super) fn flatten_single_junctions(term: &Live) -> Live {
    match term {
        Live::And(operands) | Live::Or(operands) => {
            if operands.len() == 1 {
                return flatten_single_junctions(&operands[0]);
            }
            let operands = operands.iter().map(flatten_single_junctions).collect();
            Live::junction(matches!(term, Live::And(_)), operands)
        }
        Live::Not(body) => match &**body {
            Live::Not(inner) => flatten_single_junctions(inner),
            _ => Live::not(flatten_single_junctions(body)),
        },
        Live::Always(body) => Live::always(flatten_single_junctions(body)),
        Live::Eventually(body) => Live::eventually(flatten_single_junctions(body)),
        Live::Next(body) => Live::next(flatten_single_junctions(body)),
        _ => term.clone(),
    }
}

pub(super) fn make_binary(term: &Live) -> Live {
    match term {
        Live::And(operands) | Live::Or(operands) => {
            let is_and = matches!(term, Live::And(_));
            if operands.len() == 1 {
                return make_binary(&operands[0]);
            }
            let middle = operands.len() / 2;
            let left = make_binary(&Live::junction(is_and, operands[..middle].to_vec()));
            let right = make_binary(&Live::junction(is_and, operands[middle..].to_vec()));
            Live::pair(is_and, left, right)
        }
        Live::Not(body) => Live::not(make_binary(body)),
        Live::Always(body) => Live::always(make_binary(body)),
        Live::Eventually(body) => Live::eventually(make_binary(body)),
        Live::Next(body) => Live::next(make_binary(body)),
        _ => term.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(id: usize, is_action: bool) -> Live {
        let eval = Eval { frames: crate::liveness::tests::frames(), expr: 0 };
        let kind = if is_action {
            AtomKind::Action { action: eval, unchanged: None, enabled: None, is_next: false }
        } else {
            AtomKind::State(eval)
        };
        Live::Atom(Rc::new(Atom { id, slot: 0, kind }))
    }

    #[test]
    fn negates_and_normalizes_formulas() {
        let (p, q) = (atom(1, false), atom(2, false));
        // ~[](P => <>Q) is <>(P /\ []~Q).
        let property = Live::always(Live::or(vec![Live::not(p.clone()), Live::eventually(q)]));
        let normal = simplify(&push_negation(&Live::not(property), false));
        assert_eq!(normal.key(), "Eventually(And(#1,Always(Not(#2))))");
        // Disjunctions of []<> merge into one.
        let both = Live::or(vec![
            Live::always(Live::eventually(p.clone())),
            Live::always(Live::eventually(atom(3, false))),
        ]);
        let normal = disjunctive_normal_form(&both).unwrap();
        assert_eq!(normal.key(), "Or(Always(Eventually(Or(#1,#3))))");
    }
}
