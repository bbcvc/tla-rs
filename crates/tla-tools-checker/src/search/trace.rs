//! The actions TLC names for the steps of a behavior it prints, and what the spec prints with
//! `Print` and `PrintT` as TLC computes the states of the behavior again to print them.

use tla_tools_eval::{NextAction, State};

use super::{Explorer, Successors};

/// The action of each step of a behavior, and what the spec printed computing each state again.
#[derive(Clone, Debug, Default)]
pub struct Steps {
    /// The action of each step, `None` for the initial state.
    pub actions: Vec<Option<String>>,
    /// The action of the step from the last state back to the state a lasso loops back to.
    pub loop_action: Option<String>,
    /// The lines printed computing each state again.
    pub printed: Vec<Vec<String>>,
    /// The lines printed computing the step back to the state a lasso loops back to.
    pub loop_printed: Vec<String>,
}

impl<S: Successors + ?Sized> Explorer<'_, S> {
    /// The steps of `behavior`, with the step from its last state back to the state at
    /// `loop_start`. TLC computes each step again as `Tool.getState` does, and the initial state
    /// only if `computes_initial`.
    pub(super) fn steps(
        &self,
        behavior: &[State],
        loop_start: Option<usize>,
        computes_initial: bool,
    ) -> Steps {
        let runtime = self.evaluator.runtime();
        let mut steps = Steps::default();
        if !behavior.is_empty() {
            // TLC goes through every initial state looking for the one with the fingerprint.
            let initial = || {
                let _ = self.successors.init_states(&self.plan.init, &mut |_| Ok(true));
            };
            let printed = match computes_initial {
                true => runtime.capture(initial).1,
                false => Vec::new(),
            };
            steps.actions.push(None);
            steps.printed.push(printed);
        }
        let actions = match self.plan.next.map(|next| self.evaluator.next_actions(next)) {
            Some(Ok(actions)) => actions,
            _ => {
                steps.actions.resize(behavior.len(), None);
                steps.printed.resize(behavior.len(), Vec::new());
                return steps;
            }
        };
        for step in behavior.windows(2) {
            let (action, printed) = runtime.capture(|| self.action(&actions, &step[0], &step[1]));
            steps.actions.push(action);
            steps.printed.push(printed);
        }
        if let Some((last, start)) =
            loop_start.and_then(|start| Some((behavior.last()?, behavior.get(start)?)))
        {
            let (action, printed) = runtime.capture(|| self.action(&actions, last, start));
            steps.loop_action = action;
            steps.loop_printed = printed;
        }
        steps
    }

    /// TLC's action for the step from `from` to `to` (`Tool.getState`): the first action of the
    /// split of the next-state relation with a successor of `from` that has `to`'s fingerprint.
    /// TLC computes every successor of each action it tries.
    fn action(&self, actions: &[NextAction], from: &State, to: &State) -> Option<String> {
        let wanted = self.fingerprint(to).ok()?;
        self.evaluator.runtime().set_expanding(Some(from.clone()));
        let found = actions.iter().find(|action| {
            let mut is_found = false;
            // An action that fails on this state isn't the one that took the step.
            let _ = self.evaluator.action_states(action, from, &mut |state| {
                is_found |= self.fingerprint(&state).is_ok_and(|found| found == wanted);
                Ok(true)
            });
            is_found
        });
        self.evaluator.runtime().set_expanding(None);
        found.map(|action| self.evaluator.action_label(action))
    }
}
