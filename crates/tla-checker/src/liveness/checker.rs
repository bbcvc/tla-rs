//! TLC's liveness checker: it adds each state the search finds to the behavior graph of each
//! solution, with the results of the solution's checks, and once the search is done looks for
//! a counterexample. Ported from tla-ts `liveness-checker.ts`.

use std::collections::HashMap;

use tla_eval::SpecExpr;
use tla_eval::{Evaluator, State};
use tla_resolve::DefId;

use super::convert::Translation;
use super::graph::{Graph, remove_repeats};
use super::lasso::{self, Lasso};
use super::live::{AtomKind, Eval, Live};
use super::tableau::{self, Solution};
use crate::plan::Plan;

/// A successor of a state in the model, with its index in the search if it was stored.
#[derive(Clone)]
pub struct LiveSuccessor {
    pub index: Option<u32>,
    pub state: State,
}

/// What the liveness checker needs of the search.
pub trait Explore {
    /// TLC's fingerprint of a state, by which it orders the successors of a state.
    fn tlc_fingerprint(&self, state: &State) -> Result<u64, String>;

    /// The successors of `state`, the state at `index`, that the constraints keep.
    fn successors(&self, index: u32, state: &State) -> Result<Vec<LiveSuccessor>, String>;
}

/// TLC's `SetOfStates` starts with room for this many states, times a factor that grows with
/// every set that outgrows it.
const SUCCESSOR_CAPACITY: usize = 16;

/// The results of evaluating the atoms. TLC evaluates every check on its own; without side
/// effects the order can't show, so the checks of one state share their results: those of one
/// addition to the graph by the state, and those of the state predicates by the index of the
/// state in the search for as long as the search runs.
#[derive(Default)]
struct Cache {
    states: HashMap<(*const tla_eval::Value, usize), bool>,
    actions: HashMap<(*const tla_eval::Value, *const tla_eval::Value), Vec<Option<bool>>>,
    /// The states the results are for, kept so that no other state takes their place.
    alive: Vec<State>,
    /// The index in the search of the states of this addition that have one.
    indices: HashMap<*const tla_eval::Value, u32>,
    /// The results of the state predicates on each state of the search, by its index and the
    /// predicate's slot: 0 when unknown, 1 for false, 2 for true.
    known: Vec<u8>,
    /// The number of state predicates.
    width: usize,
    /// Whether the index of a state stands for the state alone, so that results by index can
    /// be shared.
    is_shared: bool,
}

impl Cache {
    /// Forgets what is only known for one addition to the graph.
    fn reset(&mut self) {
        self.states.clear();
        self.actions.clear();
        self.alive.clear();
        self.indices.clear();
    }

    /// Notes the index of a state of this addition.
    fn index(&mut self, state: &State, index: u32) {
        if !self.is_shared {
            return;
        }
        self.indices.insert(key(state), index);
        self.alive.push(state.clone());
    }

    fn known(&self, state: &State, slot: usize) -> Option<bool> {
        let index = *self.indices.get(&key(state))? as usize;
        match self.known.get(index * self.width + slot) {
            Some(1) => Some(false),
            Some(2) => Some(true),
            _ => None,
        }
    }

    fn remember(&mut self, state: &State, slot: usize, result: bool) {
        let Some(&index) = self.indices.get(&key(state)) else { return };
        let at = index as usize * self.width + slot;
        if self.known.len() <= at {
            self.known.resize((index as usize + 1) * self.width, 0);
        }
        self.known[at] = if result { 2 } else { 1 };
    }
}

pub struct Checker<'e> {
    evaluator: &'e Evaluator,
    /// The expressions the atoms evaluate.
    exprs: Vec<SpecExpr>,
    graphs: Vec<Graph>,
    /// The number of distinct action checks across the solutions.
    action_ids: usize,
    capacity: usize,
    cache: Cache,
}

fn key(state: &State) -> *const tla_eval::Value {
    state.as_ptr()
}

impl<'e> Checker<'e> {
    /// The checker of the temporal properties of `plan`, or `None` without them. `overrides`
    /// are the definitions the configuration replaces. With a `VIEW` or a `SYMMETRY`, the
    /// states the search takes for one differ, so `is_reduced` keeps the results of the state
    /// predicates from being shared between them.
    pub fn new(
        evaluator: &'e Evaluator,
        plan: &'e Plan,
        overrides: &'e HashMap<DefId, DefId>,
        is_reduced: bool,
    ) -> Result<Option<Self>, String> {
        if plan.properties.is_empty() {
            return Ok(None);
        }
        let mut translation = Translation::new(evaluator, overrides, &plan.enabled, plan.next);
        let fairness: Vec<Live> =
            plan.fairness.iter().map(|&def| translation.formula(def)).collect::<Result<_, _>>()?;
        let mut negations: Vec<Live> = plan
            .properties
            .iter()
            .map(|(_, def)| Ok(Live::not(translation.formula(*def)?)))
            .collect::<Result<_, String>>()?;
        let violation =
            if negations.len() == 1 { negations.pop().unwrap() } else { Live::or(negations) };
        let formula = if fairness.is_empty() {
            violation
        } else {
            let mut conjuncts = fairness;
            conjuncts.push(violation);
            Live::and(conjuncts)
        };
        let solutions = tableau::solutions(&formula)?;
        if solutions.is_empty() {
            return Err("Temporal formula is a tautology (its negation is unsatisfiable).".into());
        }
        let mut ids: HashMap<String, usize> = HashMap::new();
        let graphs = solutions
            .into_iter()
            .map(|solution: Solution| {
                let action_ids = solution
                    .action_checks
                    .iter()
                    .map(|check| {
                        let next = ids.len();
                        *ids.entry(check.key()).or_insert(next)
                    })
                    .collect();
                Graph::new(solution, action_ids)
            })
            .collect();
        let width = translation.state_atoms();
        Ok(Some(Self {
            evaluator,
            exprs: translation.exprs,
            graphs,
            action_ids: ids.len(),
            capacity: 1,
            cache: Cache { width, is_shared: !is_reduced, ..Cache::default() },
        }))
    }

    /// How many solutions TLC checks, which it calls branches.
    pub fn branches(&self) -> usize {
        self.graphs.len()
    }

    /// Adds an initial state the search found new.
    pub fn add_initial_state(&mut self, index: u32, state: &State) -> Result<(), String> {
        self.cache.reset();
        self.cache.index(state, index);
        for position in 0..self.graphs.len() {
            let Some(tableau) = &self.graphs[position].solution.tableau else {
                self.graphs[position].initial.push(index);
                continue;
            };
            let consistent: Vec<usize> = (0..tableau.initial)
                .filter_map(|node| {
                    let predicates = &tableau.nodes[node].state_predicates;
                    match all_hold(self.evaluator, &self.exprs, &mut self.cache, predicates, state)
                    {
                        Ok(true) => Some(Ok(node)),
                        Ok(false) => None,
                        Err(error) => Some(Err(error)),
                    }
                })
                .collect::<Result<_, _>>()?;
            let graph = &mut self.graphs[position];
            for node in consistent {
                let node = node as u32;
                let id = match graph.node_id(index, node) {
                    Some(id) => id,
                    None => graph.record_node(index, node),
                };
                graph.initial.push(id);
            }
        }
        Ok(())
    }

    /// Adds a state the search expanded, with its successors in the model. Returns the states
    /// of a behavior that violates the properties, when TLC finds one as it adds the state.
    pub fn add_state(
        &mut self,
        index: u32,
        state: &State,
        successors: &[LiveSuccessor],
        explore: &dyn Explore,
    ) -> Result<Option<Vec<u32>>, String> {
        self.cache.reset();
        self.cache.index(state, index);
        for successor in successors {
            if let Some(successor_index) = successor.index {
                self.cache.index(&successor.state, successor_index);
            }
        }
        let set = self.successor_set(index, state, successors, explore)?;
        for position in 0..self.graphs.len() {
            let actions: Vec<Vec<bool>> = set
                .iter()
                .map(|successor| self.check_action(position, state, &successor.state))
                .collect::<Result<_, _>>()?;
            let results = self.check_state(position, state)?;
            if self.graphs[position].solution.tableau.is_none() {
                self.add_plain_state(position, &set, &actions, &results, index);
                continue;
            }
            if let Some(accepted) =
                self.add_tableau_state(position, &set, &actions, &results, index, explore)?
            {
                return Ok(Some(accepted));
            }
        }
        Ok(None)
    }

    /// The first counterexample in the graphs, once the search is done.
    pub fn find_violation(&self) -> Result<Option<Lasso>, String> {
        for graph in &self.graphs {
            for model in &graph.solution.models {
                if let Some(lasso) = lasso::find(graph, model)? {
                    return Ok(Some(lasso));
                }
            }
        }
        Ok(None)
    }

    /// The successors and the state itself in the order of TLC's `SetOfStates`, a hash set it
    /// iterates in slot order.
    fn successor_set(
        &mut self,
        index: u32,
        state: &State,
        successors: &[LiveSuccessor],
        explore: &dyn Explore,
    ) -> Result<Vec<LiveSuccessor>, String> {
        let mut slots: Vec<Option<(usize, LiveSuccessor)>> =
            vec![None; SUCCESSOR_CAPACITY * self.capacity];
        let mut count = 0;
        let itself = LiveSuccessor { index: Some(index), state: state.clone() };
        for successor in successors.iter().chain([&itself]) {
            if count >= slots.len() >> 1 {
                let grown = vec![None; 2 * slots.len() + 1];
                let old = std::mem::replace(&mut slots, grown);
                for (hash, entry) in old.into_iter().flatten() {
                    insert(&mut slots, hash, entry);
                }
            }
            let fingerprint = explore.tlc_fingerprint(&successor.state)?;
            let hash = (fingerprint as u32 as i32 & 0x7fff_ffff) as usize;
            if insert(&mut slots, hash, successor.clone()) {
                count += 1;
            }
        }
        if slots.len() > SUCCESSOR_CAPACITY * self.capacity {
            self.capacity += 1;
        }
        Ok(slots.into_iter().flatten().map(|(_, successor)| successor).collect())
    }

    fn check_state(&mut self, position: usize, state: &State) -> Result<Vec<bool>, String> {
        let checks = &self.graphs[position].solution.state_checks;
        checks
            .iter()
            .map(|check| eval(self.evaluator, &self.exprs, &mut self.cache, check, state, None))
            .collect()
    }

    fn check_action(
        &mut self,
        position: usize,
        state: &State,
        successor: &State,
    ) -> Result<Vec<bool>, String> {
        let graph = &self.graphs[position];
        let mut results = Vec::with_capacity(graph.action_ids.len());
        for (check, &id) in graph.solution.action_checks.iter().zip(&graph.action_ids) {
            let known =
                self.cache.actions.get(&(key(state), key(successor))).and_then(|known| known[id]);
            let result = match known {
                Some(result) => result,
                None => {
                    let result = eval(
                        self.evaluator,
                        &self.exprs,
                        &mut self.cache,
                        check,
                        state,
                        Some(successor),
                    )?;
                    self.cache.alive.extend([state.clone(), successor.clone()]);
                    let known = self
                        .cache
                        .actions
                        .entry((key(state), key(successor)))
                        .or_insert_with(|| vec![None; self.action_ids]);
                    known[id] = Some(result);
                    result
                }
            };
            results.push(result);
        }
        Ok(results)
    }

    fn is_consistent(&mut self, position: usize, node: u32, state: &State) -> Result<bool, String> {
        let Some(tableau) = &self.graphs[position].solution.tableau else { return Ok(true) };
        let predicates = &tableau.nodes[node as usize].state_predicates;
        all_hold(self.evaluator, &self.exprs, &mut self.cache, predicates, state)
    }

    fn tableau_successors(&self, position: usize, node: u32) -> Vec<u32> {
        let graph = &self.graphs[position];
        let tableau = graph.solution.tableau.as_ref().expect("a graph with a tableau");
        let tableau_node = graph.node_tableaux[node as usize] as usize;
        tableau.nodes[tableau_node].successors.iter().map(|&next| next as u32).collect()
    }

    /// Whether a tableau node accepts every behavior: it holds nothing and follows itself.
    fn is_accepting(&self, position: usize, node: u32) -> bool {
        let tableau = self.graphs[position].solution.tableau.as_ref();
        tableau.is_some_and(|tableau| {
            let tableau_node = &tableau.nodes[node as usize];
            tableau_node.particle.is_empty() && tableau_node.successors == [node as usize]
        })
    }

    fn add_plain_state(
        &mut self,
        position: usize,
        set: &[LiveSuccessor],
        actions: &[Vec<bool>],
        results: &[bool],
        index: u32,
    ) {
        let graph = &mut self.graphs[position];
        graph.plain_nodes_to(index);
        let mut targets: Vec<u32> = Vec::new();
        let mut edge_actions: Vec<&[bool]> = Vec::new();
        for (successor, actions) in set.iter().zip(actions) {
            let Some(successor) = successor.index else { continue };
            if graph.is_written(successor) && targets.contains(&successor) {
                continue;
            }
            targets.push(successor);
            edge_actions.push(actions);
        }
        graph.write_node(index, &targets, &edge_actions, results);
    }

    fn add_tableau_state(
        &mut self,
        position: usize,
        set: &[LiveSuccessor],
        actions: &[Vec<bool>],
        results: &[bool],
        index: u32,
        explore: &dyn Explore,
    ) -> Result<Option<Vec<u32>>, String> {
        let nodes = self.graphs[position].solution.tableau.as_ref().map_or(0, |t| t.nodes.len());
        let mut consistency = vec![Vec::with_capacity(set.len()); nodes];
        for (node, row) in consistency.iter_mut().enumerate() {
            for successor in set {
                row.push(self.is_consistent(position, node as u32, &successor.state)?);
            }
        }
        self.graphs[position].mark_done(index);
        // TLC expands the nodes recorded before the loop, not the ones the loop records.
        for node in self.graphs[position].state_nodes(index) {
            let mut targets: Vec<u32> = Vec::new();
            let mut edge_actions: Vec<usize> = Vec::new();
            let next_nodes = self.tableau_successors(position, node);
            for (place, successor) in set.iter().enumerate() {
                let Some(successor_index) = successor.index else { continue };
                let is_done = self.graphs[position].is_done(successor_index);
                for &next in &next_nodes {
                    if !consistency[next as usize][place] {
                        continue;
                    }
                    let existing = self.graphs[position].node_id(successor_index, next);
                    if existing.is_some_and(|existing| targets.contains(&existing)) {
                        continue;
                    }
                    let target = match existing {
                        Some(existing) => existing,
                        None => self.graphs[position].record_node(successor_index, next),
                    };
                    targets.push(target);
                    edge_actions.push(place);
                    if existing.is_none() && is_done {
                        self.expand_late(
                            position,
                            &successor.state,
                            successor_index,
                            target,
                            explore,
                        )?;
                    }
                }
            }
            let edge_actions: Vec<&[bool]> =
                edge_actions.iter().map(|&place| actions[place].as_slice()).collect();
            self.graphs[position].write_node(node, &targets, &edge_actions, results);
        }
        let graph = &self.graphs[position];
        let Some(error) = graph.error_node else { return Ok(None) };
        let mut path = graph.path(error)?;
        path.reverse();
        Ok(Some(remove_repeats(path.into_iter().map(|node| graph.node_states[node as usize]))))
    }

    /// TLC's `TableauLiveChecker#addNextState` for a node it finds after it expanded the
    /// node's state.
    fn expand_late(
        &mut self,
        position: usize,
        state: &State,
        index: u32,
        node: u32,
        explore: &dyn Explore,
    ) -> Result<(), String> {
        let results = self.check_state(position, state)?;
        let next_nodes = self.tableau_successors(position, node);
        let mut targets: Vec<u32> = Vec::new();
        let mut actions: Vec<Vec<bool>> = Vec::new();
        let self_actions = if next_nodes.is_empty() {
            Vec::new()
        } else {
            self.check_action(position, state, state)?
        };
        for &next in &next_nodes {
            if !self.is_consistent(position, next, state)? {
                continue;
            }
            let graph = &self.graphs[position];
            if self.is_accepting(position, next)
                && graph.error_node.is_none()
                && graph.solution.has_empty_model()
            {
                self.graphs[position].error_node = Some(node);
                return Ok(());
            }
            let existing = self.graphs[position].node_id(index, next);
            if existing.is_some_and(|existing| targets.contains(&existing)) {
                continue;
            }
            let target = match existing {
                Some(existing) => existing,
                None => self.graphs[position].record_node(index, next),
            };
            targets.push(target);
            actions.push(self_actions.clone());
            if existing.is_none() {
                self.expand_late(position, state, index, target, explore)?;
            }
        }
        for successor in explore.successors(index, state)? {
            if let Some(successor_index) = successor.index {
                self.cache.index(&successor.state, successor_index);
            }
            let successor_actions = self.check_action(position, state, &successor.state)?;
            let Some(successor_index) = successor.index else {
                // A successor the search never stored follows a violation or an error, after
                // which nothing checks the graph.
                continue;
            };
            let is_done = self.graphs[position].is_done(successor_index);
            for &next in &next_nodes {
                if !self.is_consistent(position, next, &successor.state)? {
                    continue;
                }
                let existing = self.graphs[position].node_id(successor_index, next);
                if existing.is_some_and(|existing| targets.contains(&existing)) {
                    continue;
                }
                let target = match existing {
                    Some(existing) => existing,
                    None => self.graphs[position].record_node(successor_index, next),
                };
                targets.push(target);
                actions.push(successor_actions.clone());
                if existing.is_none() && is_done {
                    self.expand_late(position, &successor.state, successor_index, target, explore)?;
                }
            }
        }
        if !targets.is_empty() {
            let actions: Vec<&[bool]> = actions.iter().map(Vec::as_slice).collect();
            self.graphs[position].write_node(node, &targets, &actions, &results);
        }
        Ok(())
    }
}

/// Inserts a successor into the slots of a `SetOfStates` by linear probing. Returns whether it
/// wasn't there.
fn insert(
    slots: &mut [Option<(usize, LiveSuccessor)>],
    hash: usize,
    successor: LiveSuccessor,
) -> bool {
    let length = slots.len();
    let mut slot = hash % length;
    loop {
        match &slots[slot] {
            None => {
                slots[slot] = Some((hash, successor));
                return true;
            }
            Some((_, entry))
                if entry.index == successor.index && same(&entry.state, &successor.state) =>
            {
                return false;
            }
            Some(_) => slot = (slot + 1) % length,
        }
    }
}

fn same(left: &State, right: &State) -> bool {
    left.iter().zip(right.iter()).all(|(left, right)| left.equals(right).unwrap_or(false))
}

fn all_hold(
    evaluator: &Evaluator,
    exprs: &[SpecExpr],
    cache: &mut Cache,
    predicates: &[Live],
    state: &State,
) -> Result<bool, String> {
    for predicate in predicates {
        if !eval(evaluator, exprs, cache, predicate, state, None)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn value(
    evaluator: &Evaluator,
    exprs: &[SpecExpr],
    eval: &Eval,
    state: &State,
    next: Option<&State>,
) -> Result<tla_eval::Value, String> {
    evaluator
        .eval_in(&eval.frames, &exprs[eval.expr], Some(state), next)
        .map_err(|error| error.to_string())
}

fn boolean(
    evaluator: &Evaluator,
    exprs: &[SpecExpr],
    eval: &Eval,
    state: &State,
    next: Option<&State>,
    what: &str,
) -> Result<bool, String> {
    let value = value(evaluator, exprs, eval, state, next)?;
    value.as_bool().ok_or_else(|| {
        format!(
            "TLC expected a boolean value, but did not find one. The value of {what} was {value}"
        )
    })
}

/// The value of a liveness formula below temporal level in `state`, or on the step to `next`.
fn eval(
    evaluator: &Evaluator,
    exprs: &[SpecExpr],
    cache: &mut Cache,
    live: &Live,
    state: &State,
    next: Option<&State>,
) -> Result<bool, String> {
    Ok(match live {
        Live::Bool(value) => *value,
        Live::Atom(atom) => match &atom.kind {
            AtomKind::State(predicate) | AtomKind::Enabled(predicate) => {
                if let Some(&known) = cache.states.get(&(key(state), atom.id)) {
                    return Ok(known);
                }
                if let Some(known) = cache.known(state, atom.slot) {
                    cache.states.insert((key(state), atom.id), known);
                    cache.alive.push(state.clone());
                    return Ok(known);
                }
                let what = "a temporal property predicate";
                let result = boolean(evaluator, exprs, predicate, state, None, what)?;
                cache.states.insert((key(state), atom.id), result);
                cache.alive.push(state.clone());
                cache.remember(state, atom.slot, result);
                result
            }
            AtomKind::Action { action, unchanged, enabled, is_next } => {
                let Some(next) = next else {
                    return Err("TLC cannot evaluate an action in a single state".into());
                };
                if let Some(enabled) = enabled
                    && cache.states.get(&(key(state), enabled.id)) == Some(&false)
                {
                    return Ok(false);
                }
                // The step of `<<A>>_v` changes `v`.
                if let Some(subscript) = unchanged {
                    let before = value(evaluator, exprs, subscript, state, None)?;
                    let after = value(evaluator, exprs, subscript, next, None)?;
                    if before.equals(&after).map_err(|error| error.to_string())? {
                        return Ok(false);
                    }
                }
                if *is_next {
                    return Ok(true);
                }
                boolean(evaluator, exprs, action, state, Some(next), "an action predicate")?
            }
        },
        Live::Not(body) => !eval(evaluator, exprs, cache, body, state, next)?,
        Live::And(operands) => {
            for operand in operands.iter() {
                if !eval(evaluator, exprs, cache, operand, state, next)? {
                    return Ok(false);
                }
            }
            true
        }
        Live::Or(operands) => {
            for operand in operands.iter() {
                if eval(evaluator, exprs, cache, operand, state, next)? {
                    return Ok(true);
                }
            }
            false
        }
        Live::Next(body) => {
            let mut fresh = Cache::default();
            eval(evaluator, exprs, &mut fresh, body, next.unwrap_or(state), None)?
        }
        Live::Always(_) | Live::Eventually(_) => {
            return Err("TLC cannot evaluate a temporal formula in a single step".into());
        }
    })
}
