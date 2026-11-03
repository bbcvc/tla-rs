//! TLC's liveness formulas and the tableau of a formula, ported from tla-ts `tableau.ts`, which
//! follows TLC's `LiveExprNode`, `TBGraph`, and `Liveness.processLiveness`.
//!
//! A formula is the negation of the properties, conjoined with the fairness of the spec. It is
//! put in disjunctive normal form, and each disjunct sorted into conditions on the cycle of a
//! behavior (`<>[]A`, `[]<>S`, `[]<>A`) and a temporal rest, whose tableau the behavior graph is
//! the product with. Disjuncts with the same rest share one tableau: a solution.

use std::collections::{HashMap, HashSet};

use tla_resolve::Level;

use super::live::AtomKind;
use super::live::{
    Live, disjunctive_normal_form, flatten_single_junctions, infinitely_often_body, is_equal,
    is_member, make_binary, push_negation, simplify,
};

fn extract_promises(term: &Live, promises: &mut Vec<Live>) {
    if matches!(term, Live::Eventually(_)) && !is_member(promises, term) {
        promises.push(term.clone());
    }
    if let Some(body) = term.body() {
        extract_promises(body, promises);
    }
    for operand in term.operands().unwrap_or_default() {
        extract_promises(operand, promises);
    }
}

fn is_locally_consistent(terms: &[Live]) -> bool {
    let negative: Vec<Live> = terms
        .iter()
        .filter_map(|term| match term {
            Live::Not(body) if body.is_state_atom() => Some((**body).clone()),
            _ => None,
        })
        .collect();
    !terms.iter().filter(|term| term.is_state_atom()).any(|term| is_member(&negative, term))
}

fn positive_closure(terms: &[Live]) -> Result<Vec<Live>, String> {
    let mut pending = terms.to_vec();
    let mut closure = Vec::new();
    while let Some(term) = pending.pop() {
        match &term {
            Live::Not(body) => pending.push((**body).clone()),
            Live::Next(body) => {
                closure.push(term.clone());
                pending.push((**body).clone());
            }
            Live::Always(body) | Live::Eventually(body) => {
                closure.push(term.clone());
                closure.push(Live::next(term.clone()));
                pending.push((**body).clone());
            }
            Live::And(operands) | Live::Or(operands) => {
                pending.extend(operands.iter().cloned());
                closure.push(term.clone());
            }
            Live::Atom(atom) if matches!(atom.kind, AtomKind::Action { .. }) => {
                return Err("TLC encountered actions while constructing the tableau".into());
            }
            _ => closure.push(term.clone()),
        }
    }
    Ok(closure)
}

/// The two parts an `alpha` (`[]`, `/\`) or `beta` (`<>`, `\/`) term splits into.
fn expansion(term: &Live, is_alpha: bool) -> Option<(Live, Live)> {
    match (term, is_alpha) {
        (Live::Always(body), true) | (Live::Eventually(body), false) => {
            Some(((**body).clone(), Live::next(term.clone())))
        }
        (Live::And(operands), true) | (Live::Or(operands), false) => {
            Some((operands[0].clone(), operands[1].clone()))
        }
        _ => None,
    }
}

struct Triple {
    whole: Live,
    first: Live,
    second: Live,
}

fn triples(closure: &[Live], is_alpha: bool) -> Vec<Triple> {
    closure
        .iter()
        .filter_map(|term| {
            let (first, second) = expansion(term, is_alpha)?;
            Some(Triple { whole: term.clone(), first, second })
        })
        .collect()
}

/// A particle is a set of terms, so its key ignores their order and repeats.
fn particle_key(particle: &[Live]) -> String {
    let keys: HashSet<String> = particle.iter().map(Live::key).collect();
    let mut keys: Vec<String> = keys.into_iter().collect();
    keys.sort();
    keys.join("|")
}

fn union_particles(left: Vec<Vec<Live>>, right: Vec<Vec<Live>>) -> Vec<Vec<Live>> {
    let right_keys: HashSet<String> = right.iter().map(|particle| particle_key(particle)).collect();
    let mut union: Vec<Vec<Live>> =
        left.into_iter().filter(|particle| !right_keys.contains(&particle_key(particle))).collect();
    union.extend(right);
    union
}

/// The particles, maximal consistent sets of terms, that `terms` expand into.
fn particle_closure(terms: &[Live]) -> Result<Vec<Vec<Live>>, String> {
    let closure = positive_closure(terms)?;
    let closure = Closure { alphas: triples(&closure, true), betas: triples(&closure, false) };
    Ok(closure.expand(terms.to_vec()))
}

struct Closure {
    alphas: Vec<Triple>,
    betas: Vec<Triple>,
}

impl Closure {
    fn expand(&self, particle: Vec<Live>) -> Vec<Vec<Live>> {
        if !is_locally_consistent(&particle) {
            return Vec::new();
        }
        let mut expanded = particle.clone();
        let mut index = 0;
        while index < expanded.len() {
            if let Some((first, second)) = expansion(&expanded[index], true) {
                if !is_member(&expanded, &first) {
                    expanded.push(first);
                }
                if !is_member(&expanded, &second) {
                    expanded.push(second);
                }
            }
            index += 1;
        }
        let mut is_changed = true;
        while is_changed {
            is_changed = false;
            for alpha in &self.alphas {
                if is_member(&expanded, &alpha.first)
                    && is_member(&expanded, &alpha.second)
                    && !is_member(&expanded, &alpha.whole)
                {
                    expanded.push(alpha.whole.clone());
                    is_changed = true;
                }
            }
        }
        if expanded.len() > particle.len() && !is_locally_consistent(&expanded) {
            return Vec::new();
        }
        self.expand_beta(expanded)
    }

    fn expand_beta(&self, particle: Vec<Live>) -> Vec<Vec<Live>> {
        for term in &particle {
            let Some((first, second)) = expansion(term, false) else { continue };
            if is_member(&particle, &first) || is_member(&particle, &second) {
                continue;
            }
            let with = |part: Live| {
                let mut extended = particle.clone();
                extended.push(part);
                extended
            };
            return union_particles(self.expand(with(first)), self.expand(with(second)));
        }
        let beta = self.betas.iter().find(|triple| {
            (is_member(&particle, &triple.first) || is_member(&particle, &triple.second))
                && !is_member(&particle, &triple.whole)
        });
        match beta {
            Some(beta) => {
                let mut extended = particle;
                extended.push(beta.whole.clone());
                self.expand(extended)
            }
            None => vec![particle],
        }
    }
}

/// A node of a tableau: a particle, the nodes that may follow it, and the terms of the particle
/// a state must satisfy to be paired with it.
#[derive(Debug)]
pub struct TableauNode {
    pub particle: Vec<Live>,
    pub successors: Vec<usize>,
    pub state_predicates: Vec<Live>,
}

/// The tableau of a formula: its first `initial` nodes are those a behavior may start in.
#[derive(Debug)]
pub struct Tableau {
    pub nodes: Vec<TableauNode>,
    pub initial: usize,
}

fn tableau_node(particle: Vec<Live>) -> TableauNode {
    // Constant terms count, as after TLC 1.7.4.
    let state_predicates =
        particle.iter().filter(|term| term.level() <= Level::State).cloned().collect();
    TableauNode { particle, successors: Vec::new(), state_predicates }
}

fn tableau(formula: &Live) -> Result<Tableau, String> {
    let mut nodes: Vec<TableauNode> =
        particle_closure(std::slice::from_ref(formula))?.into_iter().map(tableau_node).collect();
    let initial = nodes.len();
    let mut indices: HashMap<String, usize> = HashMap::new();
    for (index, node) in nodes.iter().enumerate() {
        indices.entry(particle_key(&node.particle)).or_insert(index);
    }
    let mut index = 0;
    while index < nodes.len() {
        let implied: Vec<Live> = nodes[index]
            .particle
            .iter()
            .filter_map(|term| match term {
                Live::Next(body) => Some((**body).clone()),
                _ => None,
            })
            .collect();
        for particle in particle_closure(&implied)? {
            let key = particle_key(&particle);
            let target = match indices.get(&key) {
                Some(&existing) => existing,
                None => {
                    indices.insert(key, nodes.len());
                    nodes.push(tableau_node(particle));
                    nodes.len() - 1
                }
            };
            nodes[index].successors.push(target);
        }
        index += 1;
    }
    Ok(Tableau { nodes, initial })
}

/// Whether a particle fulfills the promise `<>P`: it doesn't hold the promise, or it holds `P`.
pub fn is_fulfilling(particle: &[Live], promise: &Live) -> bool {
    let Live::Eventually(body) = promise else { return true };
    !is_member(particle, promise) || is_member(particle, body)
}

/// One way a behavior violates the properties, as conditions on its cycle: indices into the
/// state and action checks of its solution.
#[derive(Debug, Default)]
pub struct Model {
    /// `A` of `<>[]A`, which every step of the cycle must satisfy.
    pub eventually_always: Vec<usize>,
    /// `S` of `[]<>S`, which some state of the cycle must satisfy.
    pub infinitely_often_states: Vec<usize>,
    /// `A` of `[]<>A`, which some step of the cycle must satisfy.
    pub infinitely_often_actions: Vec<usize>,
}

/// The disjuncts of the formula that share a tableau.
#[derive(Debug)]
pub struct Solution {
    pub tableau: Option<Tableau>,
    /// The `<>P` terms of the tableau's formula, which a cycle must fulfill.
    pub promises: Vec<Live>,
    pub state_checks: Vec<Live>,
    pub action_checks: Vec<Live>,
    pub models: Vec<Model>,
}

impl Solution {
    /// Whether the solution constrains the cycle of a behavior, as a liveness property does
    /// (TLC's `OrderOfSolution#hasEmptyPEMAndBoxFreePromises`, negated).
    pub fn is_cycle_constrained(&self) -> bool {
        self.promises.iter().any(|promise| promise.body().is_some_and(Live::contains_always))
            || self.models.iter().any(|model| {
                !model.eventually_always.is_empty()
                    || !model.infinitely_often_states.is_empty()
                    || !model.infinitely_often_actions.is_empty()
            })
    }

    /// Whether some model has no condition on the cycle.
    pub fn has_empty_model(&self) -> bool {
        self.models.iter().any(|model| {
            model.eventually_always.is_empty()
                && model.infinitely_often_states.is_empty()
                && model.infinitely_often_actions.is_empty()
        })
    }
}

#[derive(Default)]
struct Classification {
    eventually_always: Vec<Live>,
    infinitely_often_states: Vec<Live>,
    infinitely_often_actions: Vec<Live>,
    formulas: Vec<Live>,
}

fn classify(term: &Live, classification: &mut Classification) -> Result<(), String> {
    if let Live::Eventually(body) = term
        && let Live::Always(inner) = &**body
        && inner.level() < Level::Temporal
    {
        classification.eventually_always.push((**inner).clone());
        return Ok(());
    }
    if let Some(body) = infinitely_often_body(term) {
        match body.level() {
            Level::Constant | Level::State => {
                classification.infinitely_often_states.push(body.clone());
                return Ok(());
            }
            Level::Action => {
                classification.infinitely_often_actions.push(body.clone());
                return Ok(());
            }
            Level::Temporal => {}
        }
    }
    if term.contains_action() {
        return Err("Temporal formulas containing actions must be of forms <>[]A or []<>A.".into());
    }
    classification.formulas.push(term.clone());
    Ok(())
}

fn add_to_bin(bin: &mut Vec<Live>, term: &Live) -> usize {
    if let Some(index) = bin.iter().position(|item| is_equal(item, term)) {
        return index;
    }
    bin.push(term.clone());
    bin.len() - 1
}

/// The solutions of `formula`, TLC's `OrderOfSolution`s: none when it is unsatisfiable.
pub fn solutions(formula: &Live) -> Result<Vec<Solution>, String> {
    let normal = disjunctive_normal_form(&simplify(&push_negation(formula, false)))?;
    if matches!(normal, Live::Bool(false)) {
        return Ok(Vec::new());
    }
    let disjuncts = match &normal {
        Live::Or(operands) => operands.to_vec(),
        _ => vec![normal],
    };
    let mut groups: Vec<(Option<Live>, Vec<Classification>)> = Vec::new();
    for disjunct in disjuncts {
        let flattened = flatten_single_junctions(&disjunct);
        let mut classification = Classification::default();
        let conjuncts = match &flattened {
            Live::And(operands) => operands.to_vec(),
            _ => vec![flattened],
        };
        for conjunct in &conjuncts {
            classify(conjunct, &mut classification)?;
        }
        let formulas = std::mem::take(&mut classification.formulas);
        let temporal = match formulas.len() {
            0 => None,
            1 => formulas.into_iter().next(),
            _ => Some(Live::and(formulas)),
        };
        let group = groups.iter_mut().find(|(formula, _)| match (formula, &temporal) {
            (Some(formula), Some(temporal)) => is_equal(formula, temporal),
            (None, None) => true,
            _ => false,
        });
        match group {
            Some((_, classifications)) => classifications.push(classification),
            None => groups.push((temporal, vec![classification])),
        }
    }
    groups
        .into_iter()
        .map(|(formula, classifications)| {
            let binary = formula.as_ref().map(make_binary);
            let mut promises = Vec::new();
            if let Some(binary) = &binary {
                extract_promises(binary, &mut promises);
            }
            let mut state_checks = Vec::new();
            let mut action_checks = Vec::new();
            let models = classifications
                .iter()
                .map(|classification| Model {
                    infinitely_often_actions: classification
                        .infinitely_often_actions
                        .iter()
                        .map(|check| add_to_bin(&mut action_checks, check))
                        .collect(),
                    infinitely_often_states: classification
                        .infinitely_often_states
                        .iter()
                        .map(|check| add_to_bin(&mut state_checks, check))
                        .collect(),
                    eventually_always: classification
                        .eventually_always
                        .iter()
                        .map(|check| add_to_bin(&mut action_checks, check))
                        .collect(),
                })
                .collect();
            Ok(Solution {
                tableau: binary.as_ref().map(tableau).transpose()?,
                promises,
                state_checks,
                action_checks,
                models,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;
    use crate::liveness::live::{Atom, Eval};

    fn atom(id: usize, is_action: bool) -> Live {
        let eval = Eval { frames: crate::liveness::tests::frames(), expr: 0 };
        let kind = if is_action {
            AtomKind::Action { action: eval, unchanged: None, enabled: None }
        } else {
            AtomKind::State(eval)
        };
        Live::Atom(Rc::new(Atom { id, kind }))
    }

    #[test]
    fn sorts_conditions_on_the_cycle_from_the_tableau() {
        let (p, a) = (atom(1, false), atom(2, true));
        // WF as []<>(~ENABLED \/ A), and the negated property <>[]P.
        let formula = Live::and(vec![
            Live::always(Live::eventually(Live::or(vec![Live::not(p.clone()), a]))),
            Live::eventually(Live::always(p.clone())),
        ]);
        let found = solutions(&formula).unwrap();
        assert_eq!(found.len(), 1);
        let solution = &found[0];
        assert!(solution.tableau.is_none());
        assert_eq!((solution.action_checks.len(), solution.state_checks.len()), (2, 0));
        assert_eq!(solution.models[0].eventually_always, vec![1]);
        assert_eq!(solution.models[0].infinitely_often_actions, vec![0]);
        // An action outside <>[] and []<> can't be checked.
        let error = solutions(&Live::eventually(atom(3, true))).unwrap_err();
        assert!(error.starts_with("Temporal formulas containing actions"), "{error}");
    }

    #[test]
    fn builds_the_tableau_of_a_temporal_rest() {
        let (p, q) = (atom(1, false), atom(2, false));
        // <>(P /\ []~Q): the negation of [](P => <>Q).
        let formula = Live::eventually(Live::and(vec![p, Live::always(Live::not(q))]));
        let found = solutions(&formula).unwrap();
        let tableau = found[0].tableau.as_ref().unwrap();
        assert!(tableau.initial >= 1 && tableau.nodes.len() > tableau.initial);
        assert_eq!(found[0].promises.len(), 1);
        // Every node has a successor, and some node is fulfilled.
        assert!(tableau.nodes.iter().all(|node| !node.successors.is_empty()));
        let promise = &found[0].promises[0];
        assert!(tableau.nodes.iter().any(|node| is_fulfilling(&node.particle, promise)));
        // The negation of a tautology has no solutions.
        assert!(solutions(&Live::Bool(false)).unwrap().is_empty());
    }
}
