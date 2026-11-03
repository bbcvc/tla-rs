//! What the search tells the liveness checker: each new initial state, each expanded state with
//! its successors in the model, and, once it is done, that it can look for a counterexample.

use tla_eval::{EvalError, Result, State};

use super::{Ending, Explorer, Successors, Trail};
use crate::liveness::checker::{Explore, LiveSuccessor};

fn failure(message: String) -> EvalError {
    EvalError {
        message,
        module: tla_value::Symbol::intern(""),
        span: Default::default(),
        line: 0,
        column: 0,
        incomplete: None,
    }
}

impl<S: Successors + ?Sized> Explorer<'_, S> {
    /// Adds an initial state the search found new to the behavior graph, before TLC checks its
    /// invariants.
    pub(super) fn add_live_initial_state(&self, state: &State) -> Result<()> {
        let Some(liveness) = &self.liveness else { return Ok(()) };
        let index = self.store.lock().unwrap().len() as u32;
        liveness.borrow_mut().add_initial_state(index, state).map_err(failure)
    }

    /// Adds the state the search expanded, with its successors in the model, to the behavior
    /// graph. TLC reports a violation it finds as it does.
    pub(super) fn add_live_state(
        &self,
        index: usize,
        state: &State,
        depth: u32,
        successors: &[LiveSuccessor],
    ) -> Option<(Ending, Option<Trail>)> {
        let liveness = self.liveness.as_ref()?;
        // The checks read the level of the state whose successors they check.
        self.cursor.lock().unwrap().expanding = Some((state.clone(), depth as i32, index));
        let added = liveness.borrow_mut().add_state(index as u32, state, successors, self);
        self.cursor.lock().unwrap().expanding = None;
        match added {
            Ok(None) => None,
            Ok(Some(states)) => {
                let cycle_start = states.len();
                Some((Ending::TemporalViolation, Some(Trail::Live { states, cycle_start })))
            }
            Err(message) => Some((Ending::Error(message), None)),
        }
    }

    /// The counterexample the liveness checker finds in the whole behavior graph.
    pub(super) fn find_live_violation(&self) -> Option<(Ending, Option<Trail>)> {
        let liveness = self.liveness.as_ref()?;
        match liveness.borrow().find_violation() {
            Ok(None) => None,
            Ok(Some(lasso)) => {
                let cycle_start = lasso.prefix.len();
                let mut states = lasso.prefix;
                states.extend(lasso.cycle);
                Some((Ending::LivenessViolation, Some(Trail::Live { states, cycle_start })))
            }
            Err(message) => Some((Ending::Error(message), None)),
        }
    }
}

impl<S: Successors + ?Sized> Explore for Explorer<'_, S> {
    /// TLC's own fingerprint of `state`: of its variables in TLC's order, or of its view, for
    /// the state TLC takes to stand for it under the symmetry.
    fn tlc_fingerprint(&self, state: &State) -> std::result::Result<u64, String> {
        let state = self.fingerprinter.representative(self.evaluator, state)?;
        match self.plan.view {
            Some(view) => {
                let value = self
                    .evaluator
                    .eval_def(view, Some(&state))
                    .map_err(|error| error.to_string())?;
                tla_eval::tlc_fingerprint(std::slice::from_ref(&value))
            }
            None => {
                let values: Vec<tla_eval::Value> =
                    self.tlc_order.iter().map(|&index| state[index].clone()).collect();
                tla_eval::tlc_fingerprint(&values)
            }
        }
    }

    fn successors(
        &self,
        index: u32,
        state: &State,
    ) -> std::result::Result<Vec<LiveSuccessor>, String> {
        let Some(next) = self.plan.next else { return Ok(Vec::new()) };
        let mut found = Vec::new();
        let depth = self.store.lock().unwrap().depth(index as usize);
        let expanding = self.cursor.lock().unwrap().expanding.replace((
            state.clone(),
            depth as i32,
            index as usize,
        ));
        let result = self.successors.next_states(next, state, &mut |successor| {
            let is_in_model = self.all_hold(&self.plan.constraints, &successor, None)?
                && self.all_hold(&self.plan.action_constraints, state, Some(&successor))?;
            if is_in_model {
                let fingerprint = self.fingerprint(&successor)?;
                let index = self.store.lock().unwrap().find(fingerprint).map(|index| index as u32);
                found.push(LiveSuccessor { index, state: successor });
            }
            Ok(true)
        });
        self.cursor.lock().unwrap().expanding = expanding;
        result.map_err(|error| error.to_string())?;
        Ok(found)
    }
}
