//! The search of a behavior graph for a counterexample, TLC's `LiveWorker#checkSccs`: a Tarjan
//! search for a strongly connected component that satisfies one of the solution's models, and
//! the lasso through it TLC prints (`LiveWorker#printTrace`). Ported from tla-ts
//! `liveness-checker.ts`.

use std::collections::{HashMap, HashSet};

use super::graph::{Graph, remove_repeats};
use super::tableau::{Model, is_fulfilling};

/// A behavior that violates the properties: the states before its cycle, and the cycle, by
/// index in the search.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lasso {
    pub prefix: Vec<u32>,
    pub cycle: Vec<u32>,
    /// Whether the solution constrains the cycle, as a liveness property does.
    pub is_cycle_constrained: bool,
}

const UNVISITED: i64 = -1;
const SCC_MARKER: i64 = -42;
const MAXIMUM_LINK: i64 = i64::MAX;
const FAILED: &str = "TLC failed to build the counterexample of a liveness property";

struct Search<'g> {
    graph: &'g Graph,
    model: &'g Model,
    links: Vec<i64>,
    components: Vec<u32>,
}

/// The first counterexample in `graph` that satisfies `model`.
pub fn find(graph: &Graph, model: &Model) -> Result<Option<Lasso>, String> {
    let mut search = Search {
        graph,
        model,
        links: vec![UNVISITED; graph.node_states.len()],
        components: Vec::new(),
    };
    let mut queue: Vec<u32> =
        graph.initial.iter().copied().filter(|&node| graph.is_written(node)).collect();
    let mut position = 0;
    while position < queue.len() {
        let mut stack: Vec<i64> = vec![i64::from(queue[position]), UNVISITED, 0];
        position += 1;
        let mut counter: i64 = 0;
        while stack.len() >= 3 {
            let low_link = stack.pop().unwrap_or(0);
            let location = stack.pop().unwrap_or(UNVISITED);
            let node = stack.pop().unwrap_or(0) as u32;
            if location == SCC_MARKER {
                if search.links[node as usize] == low_link
                    && let Some(lasso) = search.check_component(node)?
                {
                    return Ok(Some(lasso));
                }
                let parent = stack.pop().unwrap_or(low_link);
                stack.push(parent.min(low_link));
                continue;
            }
            if search.links[node as usize] != UNVISITED {
                stack.push(low_link.min(search.links[node as usize]));
                continue;
            }
            search.links[node as usize] = counter;
            stack.extend([low_link, i64::from(node), SCC_MARKER]);
            search.components.push(node);
            let mut next_low_link = counter;
            counter += 1;
            for (edge, &next) in graph.successors(node).iter().enumerate() {
                if !graph.is_written(next) {
                    continue;
                }
                if !search.is_allowed(node, edge) {
                    if search.links[next as usize] == UNVISITED {
                        queue.push(next);
                    }
                    continue;
                }
                if search.links[next as usize] == UNVISITED {
                    stack.extend([i64::from(next), UNVISITED]);
                } else {
                    next_low_link = next_low_link.min(search.links[next as usize]);
                }
            }
            stack.push(next_low_link);
        }
    }
    Ok(None)
}

impl Search<'_> {
    fn is_allowed(&self, node: u32, edge: usize) -> bool {
        self.model.eventually_always.iter().all(|&position| self.graph.action(node, edge, position))
    }

    fn is_stuttering(&self, node: u32) -> bool {
        let edge = self.graph.successors(node).iter().position(|&next| next == node);
        edge.is_some_and(|edge| self.is_allowed(node, edge))
    }

    fn is_fulfilled(&self, node: u32, promise: usize) -> bool {
        let solution = &self.graph.solution;
        let Some(tableau) = &solution.tableau else { return false };
        let particle = &tableau.nodes[self.graph.node_tableaux[node as usize] as usize].particle;
        is_fulfilling(particle, &solution.promises[promise])
    }

    fn check_component(&mut self, root: u32) -> Result<Option<Lasso>, String> {
        let top = self.components.pop().unwrap_or(root);
        if top == root && !self.is_stuttering(top) {
            self.links[top as usize] = MAXIMUM_LINK;
            return Ok(None);
        }
        let mut members: HashSet<u32> = HashSet::new();
        let mut members_by_state: HashMap<u32, Vec<u32>> = HashMap::new();
        let mut member = top;
        loop {
            members.insert(member);
            members_by_state
                .entry(self.graph.node_states[member as usize])
                .or_default()
                .push(member);
            self.links[member as usize] = MAXIMUM_LINK;
            if member == root {
                break;
            }
            member = self.components.pop().unwrap_or(root);
        }
        let graph = self.graph;
        let is_state_satisfied = self
            .model
            .infinitely_often_states
            .iter()
            .all(|&position| members.iter().any(|&node| graph.state_result(node, position)));
        let is_action_satisfied = self.model.infinitely_often_actions.iter().all(|&position| {
            members.iter().any(|&node| {
                graph.successors(node).iter().enumerate().any(|(edge, next)| {
                    members.contains(next)
                        && self.is_allowed(node, edge)
                        && graph.action(node, edge, position)
                })
            })
        });
        let is_promise_satisfied = (0..graph.solution.promises.len())
            .all(|promise| members.iter().any(|&node| self.is_fulfilled(node, promise)));
        if !is_state_satisfied || !is_action_satisfied || !is_promise_satisfied {
            return Ok(None);
        }
        self.lasso(root, &members, &members_by_state).map(Some)
    }

    /// TLC's `LiveWorker#printTrace`: a prefix to the root, a greedy walk through the component
    /// until it satisfies every check, and a breadth-first path back to the root.
    fn lasso(
        &self,
        root: u32,
        members: &HashSet<u32>,
        members_by_state: &HashMap<u32, Vec<u32>>,
    ) -> Result<Lasso, String> {
        let graph = self.graph;
        let model = self.model;
        let mut path = graph.path(root)?;
        path.reverse();
        let prefix = remove_repeats(path.iter().map(|&node| graph.node_states[node as usize]));
        let mut cycle_stack: Vec<u32> = Vec::new();
        let mut seen: HashSet<u32> = HashSet::from([root]);
        let mut state_done = vec![false; model.infinitely_often_states.len()];
        let mut action_done = vec![false; model.infinitely_often_actions.len()];
        let mut promise_done = vec![false; graph.solution.promises.len()];
        let mut remaining = state_done.len() + action_done.len() + promise_done.len();
        let mut current = root;
        while remaining > 0 {
            let count_at_start = remaining;
            loop {
                for (slot, &position) in model.infinitely_often_states.iter().enumerate() {
                    if !state_done[slot] && graph.state_result(current, position) {
                        state_done[slot] = true;
                        remaining -= 1;
                    }
                }
                for (promise, done) in promise_done.iter_mut().enumerate() {
                    if !*done && self.is_fulfilled(current, promise) {
                        *done = true;
                        remaining -= 1;
                    }
                }
                if remaining == 0 {
                    break;
                }
                let mut last: Option<u32> = None;
                let mut unvisited: Option<u32> = None;
                let count_before_actions = remaining;
                let mut taken = None;
                for (edge, &next) in graph.successors(current).iter().enumerate() {
                    if members_by_state.contains_key(&graph.node_states[next as usize]) {
                        if !members.contains(&next) || !self.is_allowed(current, edge) {
                            continue;
                        }
                        last = Some(next);
                        for (slot, &position) in model.infinitely_often_actions.iter().enumerate() {
                            if !action_done[slot] && graph.action(current, edge, position) {
                                action_done[slot] = true;
                                remaining -= 1;
                            }
                        }
                    }
                    if remaining < count_before_actions {
                        taken = Some(next);
                        break;
                    }
                    if members.contains(&next) && !seen.contains(&next) {
                        unvisited = Some(next);
                    }
                }
                if let Some(next) = taken {
                    cycle_stack.push(current);
                    current = next;
                    seen.clear();
                    break;
                }
                if remaining < count_at_start {
                    cycle_stack.push(current);
                    current = last.ok_or(FAILED)?;
                    seen.clear();
                    break;
                }
                while unvisited.is_none() {
                    current = cycle_stack.pop().ok_or(FAILED)?;
                    unvisited = graph
                        .successors(current)
                        .iter()
                        .copied()
                        .find(|next| members.contains(next) && !seen.contains(next));
                }
                let next = unvisited.unwrap();
                cycle_stack.push(current);
                current = next;
                seen.insert(next);
            }
        }
        let mut postfix = self.closing_path(root, current, members_by_state)?;
        for &node in cycle_stack.iter().rev() {
            let state = graph.node_states[node as usize];
            if postfix.last() != Some(&state) {
                postfix.push(state);
            }
        }
        let cycle_state = *prefix.last().ok_or(FAILED)?;
        if postfix.last() == Some(&cycle_state) {
            postfix.pop();
        }
        postfix.reverse();
        let mut cycle = vec![cycle_state];
        cycle.extend(postfix);
        Ok(Lasso {
            prefix: prefix[..prefix.len() - 1].to_vec(),
            cycle,
            is_cycle_constrained: graph.solution.is_cycle_constrained(),
        })
    }

    /// TLC's `LiveWorker#bfsPostFix`: the states from the walk's end back to the root, last
    /// first.
    fn closing_path(
        &self,
        root: u32,
        end: u32,
        members_by_state: &HashMap<u32, Vec<u32>>,
    ) -> Result<Vec<u32>, String> {
        if end == root {
            return Ok(Vec::new());
        }
        let graph = self.graph;
        let start = graph.node_states[end as usize];
        let mut parents: HashMap<u32, Option<u32>> = HashMap::new();
        let mut seen: HashSet<u32> = HashSet::from([start]);
        let mut queue: Vec<(u32, u32)> = Vec::new();
        let (mut state, mut parent) = (start, None);
        let mut position = 0;
        loop {
            for &node in members_by_state.get(&state).map(Vec::as_slice).unwrap_or_default() {
                for (edge, &next) in graph.successors(node).iter().enumerate() {
                    if next == node || !self.is_allowed(node, edge) {
                        continue;
                    }
                    if next == root {
                        let mut path = Vec::new();
                        let (mut item, mut item_parent) = (state, parent);
                        while item != start {
                            path.push(item);
                            item = item_parent.ok_or(FAILED)?;
                            item_parent = parents.get(&item).copied().flatten();
                        }
                        path.push(start);
                        return Ok(path);
                    }
                    let next_state = graph.node_states[next as usize];
                    if !members_by_state.contains_key(&next_state) || seen.contains(&next_state) {
                        continue;
                    }
                    seen.insert(next_state);
                    queue.push((next_state, state));
                }
            }
            parents.insert(state, parent);
            let &(next_state, next_parent) = queue.get(position).ok_or(FAILED)?;
            position += 1;
            state = next_state;
            parent = Some(next_parent);
        }
    }
}
