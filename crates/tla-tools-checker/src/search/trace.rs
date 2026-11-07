//! What TLC prints for the states of a behavior: the action of each step, the variables or the
//! `ALIAS` of each state, and what the spec prints with `Print` and `PrintT` as TLC computes the
//! states again and evaluates the alias, placed where TLC prints it.

use tla_tools_eval::{NextAction, State, Value};

use super::{Explorer, Successors};

/// How TLC prints a behavior, which decides when it computes the states again.
#[derive(Clone, Copy, Debug)]
pub(super) enum Shape {
    /// An initial state violates an invariant or a property: TLC prints it as it found it.
    Initial,
    /// A behavior through `stored` states the search stored, the last of which it found the
    /// violation from, to a successor of that state if `has_last`.
    Safety { stored: usize, has_last: bool },
    /// A liveness counterexample, which loops back to the state at `loop_start`, the last one
    /// for a behavior that stutters there.
    Live { loop_start: Option<usize> },
}

/// What TLC prints for each state of a behavior, and what the spec prints meanwhile.
#[derive(Clone, Debug, Default)]
pub struct Steps {
    /// The action of each step, `None` for the initial state.
    pub actions: Vec<Option<String>>,
    /// The action of the step from the last state back to the state a lasso loops back to.
    pub loop_action: Option<String>,
    /// The fields of the alias TLC prints for each state instead of its variables, if any.
    pub shown: Vec<Option<Vec<(String, Value)>>>,
    /// The lines printed before the verdict.
    pub printed_first: Vec<String>,
    /// The lines printed before the behavior's heading.
    pub printed_before: Vec<String>,
    /// The lines printed right before each state.
    pub printed: Vec<Vec<String>>,
    /// The lines printed right before the step back to the state a lasso loops back to.
    pub loop_printed: Vec<String>,
    /// The lines printed after the behavior.
    pub printed_last: Vec<String>,
}

/// What the spec printed as TLC computed each state again and evaluated its alias.
struct Computed {
    /// Computing each state, the initial one first.
    states: Vec<Vec<String>>,
    /// Evaluating the alias of each state.
    aliases: Vec<Vec<String>>,
}

impl<S: Successors + ?Sized> Explorer<'_, S> {
    /// The steps of `behavior`, which ends as `shape` says.
    ///
    /// TLC computes a state again as `Tool.getState` does: the initial one by going through
    /// every initial state, and a successor by computing every successor of each action of
    /// the next-state relation until one has its fingerprint. Each state is computed and its
    /// alias evaluated once here, and [`place`] repeats what that printed wherever TLC does it
    /// again.
    pub(super) fn steps(&self, behavior: &[State], shape: Shape) -> Steps {
        let runtime = self.evaluator.runtime();
        let mut steps = Steps::default();
        if behavior.is_empty() {
            return steps;
        }
        let loop_start = match shape {
            Shape::Live { loop_start } => loop_start,
            _ => None,
        };
        let mut computed = Computed { states: Vec::new(), aliases: Vec::new() };
        let initial = || {
            let _ = self.successors.init_states(&self.plan.init, &mut |_| Ok(true));
        };
        computed.states.push(match shape {
            Shape::Initial => Vec::new(),
            _ => runtime.capture(initial).1,
        });
        steps.actions.push(None);
        let actions = match self.plan.next.map(|next| self.evaluator.next_actions(next)) {
            Some(Ok(actions)) => actions,
            // Without the actions, TLC doesn't name the steps.
            _ => Default::default(),
        };
        for step in behavior.windows(2) {
            let (action, printed) = runtime.capture(|| self.action(&actions, &step[0], &step[1]));
            steps.actions.push(action);
            computed.states.push(printed);
        }
        // A behavior that loops back to its last state stutters there, which has no action.
        if let Some(start) = loop_start.filter(|&start| start + 1 < behavior.len()) {
            let (last, start) = (&behavior[behavior.len() - 1], &behavior[start]);
            let (action, printed) = runtime.capture(|| self.action(&actions, last, start));
            steps.loop_action = action;
            steps.loop_printed = printed;
        }
        // The alias of a state may read the next one, which is the state itself at the end.
        for (index, state) in behavior.iter().enumerate() {
            let next = behavior.get(index + 1).or_else(|| behavior.get(loop_start?));
            let (shown, printed) =
                runtime.capture(|| self.alias(state, next.unwrap_or(state), index));
            steps.shown.push(shown);
            computed.aliases.push(printed);
        }
        place(&mut steps, &computed, shape);
        steps
    }

    /// The fields of the alias in `state`, followed by `next`, the `index`th state of a
    /// behavior: `None` without an alias or for one that isn't a record, and the variables
    /// with the error for one TLC can't evaluate.
    fn alias(&self, state: &State, next: &State, index: usize) -> Option<Vec<(String, Value)>> {
        let alias = self.plan.alias.as_ref()?;
        let value = alias.as_ref().map_err(Clone::clone).and_then(|&def| {
            // `TLCGet("level")` is the state's place in the behavior.
            self.cursor.lock().unwrap().candidate = Some((state.clone(), index as i32 + 1));
            let value = self.evaluator.eval_action(def, state, next);
            self.cursor.lock().unwrap().candidate = None;
            value.map_err(|error| error.message)
        });
        match value {
            // A record has fields, each named by a string.
            Ok(Value::Func(record)) => record
                .written_entries()
                .map(|(key, value)| match key {
                    Value::Str(name) => Some((name.to_string(), value.clone())),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()
                .filter(|fields| !fields.is_empty()),
            Ok(_) => None,
            Err(message) => {
                let mut fields = self.variables(state);
                fields.push(("_ALIASEvalError".to_owned(), Value::str(&message)));
                Some(fields)
            }
        }
    }

    /// The variables of `state` and their values, in TLC's order of the variables.
    fn variables(&self, state: &State) -> Vec<(String, Value)> {
        let spec = self.evaluator.spec();
        self.tlc_order
            .iter()
            .map(|&index| (spec.variables[index].name.to_string(), state[index].clone()))
            .collect()
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

/// Puts what the spec printed where TLC prints it.
fn place(steps: &mut Steps, computed: &Computed, shape: Shape) {
    let count = computed.aliases.len();
    steps.printed = vec![Vec::new(); count];
    match shape {
        // TLC evaluates the alias of the state as it prints it, and prints the verdict with it.
        Shape::Initial => steps.printed_first = computed.aliases.concat(),
        // TLC computes again the stored states before the last one, the initial one only when
        // another follows it, and prints the heading. Then it prints each state, computing the
        // last stored one and the violating successor again first, and evaluating the alias.
        // A deadlock or an error in an initial state is printed without its alias. Then it
        // computes the whole behavior again, and evaluates the alias of each state.
        Shape::Safety { stored, has_last } => {
            let before = stored.saturating_sub(1);
            if stored >= 2 {
                for printed in computed.states.iter().take(before) {
                    steps.printed_before.extend(printed.iter().cloned());
                }
            }
            let has_alias = stored >= 2 || has_last;
            for index in 0..count {
                let printed = &mut steps.printed[index];
                if index >= before && (index > 0 || stored >= 2) {
                    printed.extend(computed.states[index].iter().cloned());
                }
                if has_alias {
                    printed.extend(computed.aliases[index].iter().cloned());
                } else {
                    steps.shown[index] = None;
                }
            }
            steps.printed_last = [computed.states.concat(), computed.aliases.concat()].concat();
        }
        // TLC computes the states up to the one the behavior loops back to, then evaluates the
        // alias of each state before it, and computes each later state, evaluating the alias of
        // the one before it, before it prints the verdict.
        Shape::Live { loop_start } => {
            let start = loop_start.unwrap_or(count - 1).min(count - 1);
            let first = &mut steps.printed_first;
            for printed in &computed.states[..=start] {
                first.extend(printed.iter().cloned());
            }
            for printed in &computed.aliases[..start] {
                first.extend(printed.iter().cloned());
            }
            for index in start + 1..count {
                first.extend(computed.states[index].iter().cloned());
                first.extend(computed.aliases[index - 1].iter().cloned());
            }
            first.extend(computed.aliases[count - 1].iter().cloned());
        }
    }
}
