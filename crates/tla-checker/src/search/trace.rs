//! The actions TLC names for the steps of a behavior it prints.

use tla_eval::{NextAction, State};

use super::{Explorer, Successors};

impl<S: Successors + ?Sized> Explorer<'_, S> {
    /// The action of each step of `behavior`, and of the step from its last state back to the
    /// state at `loop_start`: `None` for the initial state.
    pub(super) fn actions(
        &self,
        behavior: &[State],
        loop_start: Option<usize>,
    ) -> (Vec<Option<String>>, Option<String>) {
        let actions = match self.plan.next.map(|next| self.evaluator.next_actions(next)) {
            Some(Ok(actions)) => actions,
            _ => return (vec![None; behavior.len()], None),
        };
        let mut labels = Vec::with_capacity(behavior.len());
        labels.extend(behavior.first().map(|_| None));
        labels.extend(behavior.windows(2).map(|step| self.action(&actions, &step[0], &step[1])));
        let back = loop_start
            .and_then(|start| Some((behavior.last()?, behavior.get(start)?)))
            .and_then(|(last, start)| self.action(&actions, last, start));
        (labels, back)
    }

    /// TLC's action for the step from `from` to `to` (`Tool.getState`): the first action of the
    /// split of the next-state relation with a successor of `from` that has `to`'s fingerprint.
    fn action(&self, actions: &[NextAction], from: &State, to: &State) -> Option<String> {
        let wanted = self.fingerprint(to).ok()?;
        self.evaluator.runtime().set_expanding(Some(from.clone()));
        let found = actions.iter().find(|action| {
            let mut is_found = false;
            // An action that fails on this state isn't the one that took the step.
            let _ = self.evaluator.action_states(action, from, &mut |state| {
                is_found = self.fingerprint(&state).is_ok_and(|found| found == wanted);
                Ok(!is_found)
            });
            is_found
        });
        self.evaluator.runtime().set_expanding(None);
        found.map(|action| self.evaluator.action_label(action))
    }
}
