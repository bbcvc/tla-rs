//! The states a search has found, as TLC keeps them: the fingerprint of each, the state it was
//! found from, and its depth. TLC keeps no state once it has expanded it, and rebuilds a trace
//! from the fingerprints. This keeps the states too only when the spec reads behaviors as it
//! runs, through `TLCExt!Trace`.

use hashbrown::HashTable;
use tla_eval::State;

/// The parent of an initial state.
const NONE: u32 = u32::MAX;

pub struct Store {
    /// The index of each state, found by its fingerprint.
    table: HashTable<u32>,
    fingerprints: Vec<u128>,
    parents: Vec<u32>,
    depths: Vec<u32>,
    states: Option<Vec<State>>,
}

impl Store {
    pub fn new(keeps_states: bool) -> Self {
        Self {
            table: HashTable::new(),
            fingerprints: Vec::new(),
            parents: Vec::new(),
            depths: Vec::new(),
            states: keeps_states.then(Vec::new),
        }
    }

    pub fn len(&self) -> usize {
        self.fingerprints.len()
    }

    pub fn contains(&self, fingerprint: u128) -> bool {
        self.find(fingerprint).is_some()
    }

    /// The index of the state with `fingerprint`.
    pub fn find(&self, fingerprint: u128) -> Option<usize> {
        let fingerprints = &self.fingerprints;
        let found = self
            .table
            .find(fingerprint as u64, |&index| fingerprints[index as usize] == fingerprint);
        found.map(|&index| index as usize)
    }

    /// Adds a state not found before, and returns its index.
    pub fn insert(
        &mut self,
        fingerprint: u128,
        state: &State,
        parent: Option<usize>,
        depth: u32,
    ) -> usize {
        let index = self.fingerprints.len();
        let fingerprints = &self.fingerprints;
        self.table.insert_unique(fingerprint as u64, index as u32, |&index| {
            fingerprints[index as usize] as u64
        });
        self.fingerprints.push(fingerprint);
        self.parents.push(parent.map_or(NONE, |parent| parent as u32));
        self.depths.push(depth);
        if let Some(states) = &mut self.states {
            states.push(state.clone());
        }
        index
    }

    pub fn depth(&self, index: usize) -> u32 {
        self.depths[index]
    }

    /// The indices of the states from an initial state to the state at `index`.
    pub fn lineage(&self, index: usize) -> Vec<usize> {
        let mut lineage = vec![index];
        let mut current = index;
        while self.parents[current] != NONE {
            current = self.parents[current] as usize;
            lineage.push(current);
        }
        lineage.reverse();
        lineage
    }

    pub fn fingerprint(&self, index: usize) -> u128 {
        self.fingerprints[index]
    }

    /// The behavior to the state at `index`, if the store keeps states.
    pub fn path(&self, index: usize) -> Option<Vec<State>> {
        let states = self.states.as_ref()?;
        Some(self.lineage(index).into_iter().map(|index| states[index].clone()).collect())
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use tla_value::Value;

    use super::*;

    fn state(x: i32) -> State {
        Arc::from(vec![Value::Int(x)])
    }

    #[test]
    fn keeps_fingerprints_and_how_each_state_was_reached() {
        let mut store = Store::new(true);
        assert_eq!(store.insert(10, &state(0), None, 1), 0);
        assert_eq!(store.insert(11, &state(1), Some(0), 2), 1);
        assert_eq!(store.insert(12, &state(2), Some(1), 3), 2);
        // Fingerprints that agree in their low 64 bits are still told apart.
        assert_eq!(store.insert(12 | (1 << 64), &state(3), Some(0), 2), 3);
        assert!(store.contains(12) && store.contains(12 | (1 << 64)) && !store.contains(13));
        assert_eq!((store.len(), store.depth(2)), (4, 3));
        assert_eq!(store.lineage(2), vec![0, 1, 2]);
        let path = store.path(3).unwrap();
        assert_eq!(path.len(), 2);
        assert!(Store::new(false).path(0).is_none());
    }
}
