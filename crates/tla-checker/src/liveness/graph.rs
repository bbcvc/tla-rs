//! TLC's behavior graph for one solution of the liveness formula: a node for each state the
//! search finds, or for each pair of a state and a node of the solution's tableau that the state
//! satisfies, with the results of the solution's checks on each state and step. Ported from
//! tla-ts `liveness-checker.ts`, which follows TLC's `TableauLiveChecker`, `LiveChecker`, and
//! `GraphNode`.

use std::collections::HashMap;

use super::tableau::Solution;

const NO_NODE: u32 = u32::MAX;

/// A state's node in a graph without a tableau, which has one node per state.
pub const PLAIN: u32 = u32::MAX;

pub struct Graph {
    pub solution: Solution,
    /// The id of each of the solution's action checks among those of all solutions, so that
    /// the checks shared between solutions are evaluated once on a step.
    pub action_ids: Vec<usize>,
    pub node_states: Vec<u32>,
    /// The tableau node of each node, [`PLAIN`] without a tableau.
    pub node_tableaux: Vec<u32>,
    /// Where each node's successors start in `edge_targets`, `None` until the node is
    /// written with its successors.
    edge_starts: Vec<Option<u32>>,
    edge_counts: Vec<u32>,
    edge_targets: Vec<u32>,
    /// The results of the action checks on each edge, by the edge's position in
    /// `edge_targets`.
    edge_actions: Vec<bool>,
    /// The results of the state checks on each state.
    state_results: Vec<bool>,
    pub initial: Vec<u32>,
    /// The nodes of each state, in the order they are recorded, a list through `next_siblings`.
    first_nodes: Vec<u32>,
    last_nodes: Vec<u32>,
    next_siblings: Vec<u32>,
    node_ids: HashMap<(u32, u32), u32>,
    /// Whether each state has been added with its successors.
    pub is_done: Vec<bool>,
    pub error_node: Option<u32>,
}

impl Graph {
    pub fn new(solution: Solution, action_ids: Vec<usize>) -> Self {
        Self {
            solution,
            action_ids,
            node_states: Vec::new(),
            node_tableaux: Vec::new(),
            edge_starts: Vec::new(),
            edge_counts: Vec::new(),
            edge_targets: Vec::new(),
            edge_actions: Vec::new(),
            state_results: Vec::new(),
            initial: Vec::new(),
            first_nodes: Vec::new(),
            last_nodes: Vec::new(),
            next_siblings: Vec::new(),
            node_ids: HashMap::new(),
            is_done: Vec::new(),
            error_node: None,
        }
    }

    pub fn is_written(&self, node: u32) -> bool {
        self.edge_starts.get(node as usize).is_some_and(Option::is_some)
    }

    pub fn successors(&self, node: u32) -> &[u32] {
        match self.edge_starts.get(node as usize).copied().flatten() {
            Some(start) => {
                let start = start as usize;
                &self.edge_targets[start..start + self.edge_counts[node as usize] as usize]
            }
            None => &[],
        }
    }

    pub fn state_result(&self, node: u32, position: usize) -> bool {
        let checks = self.solution.state_checks.len();
        let state = self.node_states[node as usize] as usize;
        self.state_results.get(state * checks + position).copied().unwrap_or(false)
    }

    pub fn action(&self, node: u32, edge: usize, position: usize) -> bool {
        let checks = self.solution.action_checks.len();
        let Some(start) = self.edge_starts[node as usize] else { return false };
        self.edge_actions[(start as usize + edge) * checks + position]
    }

    fn push_node(&mut self, state: u32, tableau: u32) -> u32 {
        self.node_states.push(state);
        self.node_tableaux.push(tableau);
        self.edge_starts.push(None);
        self.edge_counts.push(0);
        self.next_siblings.push(NO_NODE);
        self.node_states.len() as u32 - 1
    }

    /// The node of a state with a tableau node, if recorded; a state's own node without a
    /// tableau.
    pub fn node_id(&self, state: u32, tableau: u32) -> Option<u32> {
        if self.solution.tableau.is_none() {
            return Some(state);
        }
        self.node_ids.get(&(state, tableau)).copied()
    }

    pub fn record_node(&mut self, state: u32, tableau: u32) -> u32 {
        let node = self.push_node(state, tableau);
        self.node_ids.insert((state, tableau), node);
        let state = state as usize;
        if self.first_nodes.len() <= state {
            self.first_nodes.resize(state + 1, NO_NODE);
            self.last_nodes.resize(state + 1, NO_NODE);
        }
        match self.last_nodes[state] {
            NO_NODE => self.first_nodes[state] = node,
            last => self.next_siblings[last as usize] = node,
        }
        self.last_nodes[state] = node;
        node
    }

    /// The nodes recorded for a state, in order.
    pub fn state_nodes(&self, state: u32) -> Vec<u32> {
        let mut nodes = Vec::new();
        let mut node = self.first_nodes.get(state as usize).copied().unwrap_or(NO_NODE);
        while node != NO_NODE {
            nodes.push(node);
            node = self.next_siblings[node as usize];
        }
        nodes
    }

    /// Writes a node's successors with the results of the action checks on each edge, and its
    /// state's results.
    pub fn write_node(
        &mut self,
        node: u32,
        targets: &[u32],
        actions: &[&[bool]],
        state_results: &[bool],
    ) {
        let start = self.edge_targets.len();
        let checks = self.solution.action_checks.len();
        self.edge_targets.extend_from_slice(targets);
        self.edge_actions.resize(self.edge_targets.len() * checks, false);
        for (position, results) in actions.iter().enumerate() {
            let offset = (start + position) * checks;
            self.edge_actions[offset..offset + checks].copy_from_slice(results);
        }
        let state = self.node_states[node as usize] as usize;
        let offset = state * state_results.len();
        if self.state_results.len() < offset + state_results.len() {
            self.state_results.resize(offset + state_results.len(), false);
        }
        self.state_results[offset..offset + state_results.len()].copy_from_slice(state_results);
        self.edge_starts[node as usize] = Some(start as u32);
        self.edge_counts[node as usize] = targets.len() as u32;
    }

    /// Makes sure a graph without a tableau has a node for each state up to `state`.
    pub fn plain_nodes_to(&mut self, state: u32) {
        while self.node_states.len() <= state as usize {
            let next = self.node_states.len() as u32;
            self.push_node(next, PLAIN);
        }
    }

    pub fn mark_done(&mut self, state: u32) {
        let state = state as usize;
        if self.is_done.len() <= state {
            self.is_done.resize(state + 1, false);
        }
        self.is_done[state] = true;
    }

    pub fn is_done(&self, state: u32) -> bool {
        self.is_done.get(state as usize).copied().unwrap_or(false)
    }

    /// The shortest path from an initial node to `target`, last node first, as TLC's
    /// `getPath` finds it.
    pub fn path(&self, target: u32) -> Result<Vec<u32>, String> {
        if self.initial.contains(&target) {
            return Ok(vec![target]);
        }
        let mut parents: HashMap<u32, Option<u32>> = HashMap::new();
        let mut queue: Vec<u32> = Vec::new();
        for &node in &self.initial {
            if !self.is_written(node) {
                continue;
            }
            queue.push(node);
            parents.insert(node, None);
        }
        let mut position = 0;
        while position < queue.len() {
            let current = queue[position];
            position += 1;
            for &next in self.successors(current) {
                if next == current && self.solution.tableau.is_some() {
                    continue;
                }
                if next == target {
                    let mut path = vec![target];
                    let mut node = Some(current);
                    while let Some(found) = node {
                        path.push(found);
                        node = parents.get(&found).copied().flatten();
                    }
                    return Ok(path);
                }
                if !self.is_written(next) || parents.contains_key(&next) {
                    continue;
                }
                parents.insert(next, Some(current));
                queue.push(next);
            }
        }
        Err(format!("Couldn't re-create liveness trace (path) starting at: {target}"))
    }
}

/// The states of a path, without repeats of a state in a row.
pub fn remove_repeats(path: impl IntoIterator<Item = u32>) -> Vec<u32> {
    let mut states: Vec<u32> = Vec::new();
    for state in path {
        if states.last() != Some(&state) {
            states.push(state);
        }
    }
    states
}
