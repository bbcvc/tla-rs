//! Breadth-first search of the state graph, as TLC's model checker explores it with one worker:
//! a set of the fingerprints of the states found, a FIFO queue of those to expand, and a link
//! from each state to the one it was found from, for traces. It counts the states generated,
//! repeats and initial states included, and the distinct states, as TLC does.

use std::collections::HashSet;
use std::hash::{DefaultHasher, Hasher};
use std::sync::{Arc, Mutex};

use tla_eval::{EvalError, Evaluator, Result, State, Statistics};
use tla_resolve::DefId;
use tla_value::Value;

use crate::plan::{Check, Plan};

/// The states of a model, which the model checker explores: TLC's order of the initial states
/// and of the successors of a state, repeats included.
pub trait Successors {
    /// Each state satisfying the conjunction of the zero-arity definitions `init`. `found`
    /// returns `Ok(false)` to stop.
    fn init_states(
        &self,
        init: &[DefId],
        found: &mut dyn FnMut(State) -> Result<bool>,
    ) -> Result<()>;

    /// Each successor of `state` under the zero-arity action `next`, without stuttering steps.
    fn next_states(
        &self,
        next: DefId,
        state: &State,
        found: &mut dyn FnMut(State) -> Result<bool>,
    ) -> Result<()>;
}

/// How a search ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ending {
    Success,
    /// An invariant failed in the last state of the trace.
    InvariantViolation(String),
    /// A property TLC checks on the initial states or on each step failed, which TLC reports
    /// as a liveness violation.
    PropertyViolation(String),
    Deadlock,
    /// Evaluation failed.
    Error(String),
}

/// The result of a search: how it ended, the behavior that ends in the violation, and TLC's
/// counts.
#[derive(Clone, Debug)]
pub struct Search {
    pub ending: Ending,
    pub trace: Vec<State>,
    pub generated: u64,
    pub distinct: u64,
    pub depth: u64,
}

/// What `TLCGet("level")` reads: the state the model checker expands and the one it checks.
#[derive(Default)]
struct Cursor {
    expanding: Option<(State, i32)>,
    candidate: Option<(State, i32)>,
}

impl Cursor {
    fn level(&self, state: &State) -> i32 {
        if let Some((candidate, level)) = &self.candidate
            && Arc::ptr_eq(candidate, state)
        {
            return *level;
        }
        match &self.expanding {
            Some((expanding, level)) if Arc::ptr_eq(expanding, state) => *level,
            Some((_, level)) => level + 1,
            None => 0,
        }
    }
}

/// The states found, with how each was reached, which `TLCExt!Trace` reads.
#[derive(Default)]
struct Graph {
    states: Vec<State>,
    /// The index of the state each was found from, `None` for an initial state.
    parents: Vec<Option<u32>>,
    depths: Vec<u32>,
}

impl Graph {
    fn path(&self, index: usize) -> Vec<State> {
        let mut path = Vec::new();
        let mut current = Some(index as u32);
        while let Some(index) = current {
            path.push(self.states[index as usize].clone());
            current = self.parents[index as usize];
        }
        path.reverse();
        path
    }

    fn find(&self, state: &State) -> Option<usize> {
        self.states.iter().position(|found| Arc::ptr_eq(found, state))
    }
}

/// A fingerprint that agrees with value equality, wide enough that two distinct states don't
/// share one in practice.
fn fingerprint(state: &[Value]) -> std::result::Result<u128, String> {
    let mut halves = [DefaultHasher::new(), DefaultHasher::new()];
    halves[1].write_u8(0x5a);
    for hasher in &mut halves {
        for value in state {
            value.fingerprint(hasher).map_err(|error| error.to_string())?;
        }
    }
    Ok((u128::from(halves[0].finish()) << 64) | u128::from(halves[1].finish()))
}

struct Explorer<'a, S: Successors + ?Sized> {
    successors: &'a S,
    evaluator: &'a Evaluator,
    plan: &'a Plan,
    check_deadlock: bool,
    seen: HashSet<u128>,
    graph: Arc<Mutex<Graph>>,
    cursor: Arc<Mutex<Cursor>>,
    generated: u64,
    initial: u64,
    depth: u32,
}

/// What a visit to a state found.
enum Visit {
    Continue,
    Stop(Ending, Vec<State>),
}

/// Explores the states of `plan` breadth first.
pub fn search<S: Successors + ?Sized>(
    successors: &S,
    evaluator: &Evaluator,
    plan: &Plan,
    check_deadlock: bool,
) -> Search {
    let graph = Arc::new(Mutex::new(Graph::default()));
    let cursor = Arc::new(Mutex::new(Cursor::default()));
    let runtime = evaluator.runtime();
    let level = cursor.clone();
    runtime.on_level(move |state| level.lock().unwrap().level(state));
    let behavior = graph.clone();
    let behavior_cursor = cursor.clone();
    runtime.on_behavior(move |state| {
        let graph = behavior.lock().unwrap();
        if let Some(index) = graph.find(state) {
            return graph.path(index);
        }
        // A state being checked follows the one being expanded.
        let expanding = behavior_cursor.lock().unwrap().expanding.clone();
        let mut path = match expanding.and_then(|(expanding, _)| graph.find(&expanding)) {
            Some(index) => graph.path(index),
            None => Vec::new(),
        };
        path.push(state.clone());
        path
    });
    let mut explorer = Explorer {
        successors,
        evaluator,
        plan,
        check_deadlock,
        seen: HashSet::new(),
        graph,
        cursor,
        generated: 0,
        initial: 0,
        depth: 0,
    };
    let (ending, trace) = explorer.run();
    let distinct = explorer.graph.lock().unwrap().states.len() as u64;
    Search {
        ending,
        trace,
        generated: explorer.generated,
        distinct,
        depth: if explorer.generated == 0 { 0 } else { u64::from(explorer.depth.max(1)) },
    }
}

impl<S: Successors + ?Sized> Explorer<'_, S> {
    fn run(&mut self) -> (Ending, Vec<State>) {
        let mut stopped = None;
        let (successors, init) = (self.successors, &self.plan.init);
        let result = successors.init_states(init, &mut |state| match self.visit_initial(state)? {
            Visit::Continue => Ok(true),
            Visit::Stop(ending, trace) => {
                stopped = Some((ending, trace));
                Ok(false)
            }
        });
        self.cursor.lock().unwrap().candidate = None;
        if let Err(error) = result {
            return (Ending::Error(error.to_string()), Vec::new());
        }
        if let Some(stopped) = stopped {
            return stopped;
        }
        let Some(next) = self.plan.next else {
            if self.graph.lock().unwrap().states.is_empty() {
                return (Ending::Success, Vec::new());
            }
            let message = "No next state actions defined to generate successor states from.";
            return (Ending::Error(message.into()), Vec::new());
        };
        let mut index = 0;
        loop {
            if self.evaluator.runtime().is_stopped.load(std::sync::atomic::Ordering::Relaxed) {
                break;
            }
            let (state, depth) = {
                let graph = self.graph.lock().unwrap();
                match graph.states.get(index) {
                    Some(state) => (state.clone(), graph.depths[index]),
                    None => break,
                }
            };
            self.cursor.lock().unwrap().expanding = Some((state.clone(), depth as i32));
            self.update_statistics(index);
            // TLC seeds a worker's random choices with the fingerprint of the state it expands.
            self.evaluator.runtime().set_expanding(Some(state.clone()));
            let mut count = 0u64;
            let mut stopped = None;
            let successors = self.successors;
            let result = successors.next_states(next, &state, &mut |successor| {
                count += 1;
                match self.visit_successor(index, &state, depth, successor)? {
                    Visit::Continue => Ok(true),
                    Visit::Stop(ending, trace) => {
                        stopped = Some((ending, trace));
                        Ok(false)
                    }
                }
            });
            self.evaluator.runtime().set_expanding(None);
            {
                let mut cursor = self.cursor.lock().unwrap();
                cursor.candidate = None;
                cursor.expanding = None;
            }
            if let Err(error) = result {
                return (Ending::Error(error.to_string()), self.graph.lock().unwrap().path(index));
            }
            if let Some(stopped) = stopped {
                return stopped;
            }
            if count == 0 && self.check_deadlock {
                return (Ending::Deadlock, self.graph.lock().unwrap().path(index));
            }
            index += 1;
        }
        (Ending::Success, Vec::new())
    }

    fn update_statistics(&self, expanding: usize) {
        let distinct = self.graph.lock().unwrap().states.len() as i64;
        let (generated, initial, depth) = (self.generated as i64, self.initial as i64, self.depth);
        self.evaluator.runtime().update_statistics(|statistics: &mut Statistics| {
            statistics.generated = generated;
            statistics.distinct = distinct;
            statistics.initial = initial;
            statistics.queue = (distinct - expanding as i64 - 1).max(0);
            statistics.diameter = i64::from(depth);
        });
    }

    fn holds(&self, check: &Check, state: &State, next: Option<&State>) -> Result<bool> {
        let value = match next {
            Some(next) => self.evaluator.eval_action(check.def, state, next)?,
            None => self.evaluator.eval_def(check.def, Some(state))?,
        };
        value.as_bool().ok_or_else(|| self.not_boolean(check, &value))
    }

    fn not_boolean(&self, check: &Check, value: &Value) -> EvalError {
        let spec = self.evaluator.spec();
        let def = spec.def(check.def);
        let module = &spec.modules[def.module.index()];
        let (line, column) = def.span.line_column(&module.source);
        EvalError {
            message: format!(
                "TLC expected a boolean value, but did not find one. {} is {value}",
                check.name
            ),
            module: module.name,
            span: def.span,
            line,
            column,
        }
    }

    fn all_hold(&self, checks: &[Check], state: &State, next: Option<&State>) -> Result<bool> {
        for check in checks {
            if !self.holds(check, state, next)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn first_failing<'c>(
        &self,
        checks: &'c [Check],
        state: &State,
        next: Option<&State>,
    ) -> Result<Option<&'c Check>> {
        for check in checks {
            if !self.holds(check, state, next)? {
                return Ok(Some(check));
            }
        }
        Ok(None)
    }

    fn fingerprint(&self, state: &State) -> Result<u128> {
        fingerprint(state).map_err(|message| EvalError {
            message,
            module: tla_value::Symbol::intern(""),
            span: Default::default(),
            line: 0,
            column: 0,
        })
    }

    fn store(&mut self, fingerprint: u128, state: State, parent: Option<usize>, depth: u32) {
        self.seen.insert(fingerprint);
        self.depth = self.depth.max(depth);
        let mut graph = self.graph.lock().unwrap();
        graph.states.push(state);
        graph.parents.push(parent.map(|parent| parent as u32));
        graph.depths.push(depth);
    }

    /// TLC's `ModelChecker.checkInitialState` with one worker.
    fn visit_initial(&mut self, state: State) -> Result<Visit> {
        self.generated += 1;
        self.initial += 1;
        self.cursor.lock().unwrap().candidate = Some((state.clone(), 1));
        let is_in_model = self.all_hold(&self.plan.constraints, &state, None)?;
        let fingerprint = self.fingerprint(&state)?;
        if is_in_model && self.seen.contains(&fingerprint) {
            return Ok(Visit::Continue);
        }
        if let Some(check) = self.first_failing(&self.plan.invariants, &state, None)? {
            let ending = Ending::InvariantViolation(check.name.clone());
            return Ok(Visit::Stop(ending, vec![state]));
        }
        if let Some(check) = self.first_failing(&self.plan.initial_predicates, &state, None)? {
            let ending = Ending::PropertyViolation(check.name.clone());
            return Ok(Visit::Stop(ending, vec![state]));
        }
        if is_in_model {
            self.store(fingerprint, state, None, 1);
        }
        self.update_statistics(0);
        Ok(Visit::Continue)
    }

    /// TLC's worker checking a successor of the state it expands.
    fn visit_successor(
        &mut self,
        parent: usize,
        state: &State,
        depth: u32,
        successor: State,
    ) -> Result<Visit> {
        self.generated += 1;
        self.cursor.lock().unwrap().candidate = Some((successor.clone(), depth as i32 + 1));
        let fingerprint = self.fingerprint(&successor)?;
        let is_found = self.seen.contains(&fingerprint);
        let is_in_model = self.all_hold(&self.plan.constraints, &successor, None)?
            && self.all_hold(&self.plan.action_constraints, state, Some(&successor))?;
        let is_new = is_in_model && !is_found;
        let trace = || {
            let mut trace = self.graph.lock().unwrap().path(parent);
            trace.push(successor.clone());
            trace
        };
        // TLC checks the invariants of a state it hasn't stored, one the constraints exclude
        // included.
        if !(is_in_model && is_found)
            && let Some(check) = self.first_failing(&self.plan.invariants, &successor, None)?
        {
            return Ok(Visit::Stop(Ending::InvariantViolation(check.name.clone()), trace()));
        }
        let property = self.first_failing(&self.plan.action_properties, state, Some(&successor))?;
        if let Some(check) = property {
            return Ok(Visit::Stop(Ending::PropertyViolation(check.name.clone()), trace()));
        }
        if is_new {
            self.store(fingerprint, successor, Some(parent), depth + 1);
        }
        Ok(Visit::Continue)
    }
}

#[cfg(test)]
mod tests {
    use crate::Status;
    use crate::testing::{System, run};

    const SPEC: &str = "Init == x = 0\nNext == x' = x + 1\nSpec == Init /\\ [][Next]_x";

    fn counter(x: i32) -> Vec<i32> {
        if x < 3 { vec![x + 1] } else { Vec::new() }
    }

    /// 0 goes to 1 and 2, both go to 3, and 3 to itself.
    fn diamond(x: i32) -> Vec<i32> {
        match x {
            0 => vec![1, 2],
            1 | 2 => vec![3],
            _ => vec![3],
        }
    }

    fn counts(outcome: &crate::Outcome) -> (Status, Option<u64>, Option<u64>, Option<u64>) {
        (outcome.status, outcome.generated, outcome.distinct, outcome.depth)
    }

    #[test]
    fn counts_states_as_tlc_does() {
        let config = "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE";
        let outcome = run(SPEC, config, System { init: vec![0], next: counter });
        assert_eq!(counts(&outcome), (Status::Success, Some(4), Some(4), Some(4)));
        // Repeats count as generated, and the initial states too.
        let outcome = run(SPEC, config, System { init: vec![0, 0], next: diamond });
        assert_eq!(counts(&outcome), (Status::Success, Some(7), Some(4), Some(3)));
    }

    #[test]
    fn reports_a_deadlock_with_the_behavior_to_it() {
        let outcome = run(SPEC, "SPECIFICATION Spec", System { init: vec![0], next: counter });
        assert_eq!((outcome.status, outcome.trace_length), (Status::Deadlock, Some(4)));
        // A state whose only successor is itself isn't deadlocked.
        let outcome = run(SPEC, "SPECIFICATION Spec", System { init: vec![0], next: diamond });
        assert_eq!(outcome.status, Status::Success);
    }

    #[test]
    fn reports_the_invariant_a_state_violates() {
        let body = format!("{SPEC}\nSmall == x < 2\nPositive == x > 0");
        let config = "SPECIFICATION Spec\nINVARIANT Small";
        let outcome = run(&body, config, System { init: vec![0], next: counter });
        assert_eq!(outcome.status, Status::InvariantViolation);
        assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Small"), Some(3)));
        let config = "SPECIFICATION Spec\nINVARIANT Positive";
        let outcome = run(&body, config, System { init: vec![0], next: counter });
        assert_eq!(
            (outcome.violation.as_deref(), outcome.trace_length),
            (Some("Positive"), Some(1))
        );
    }

    #[test]
    fn leaves_out_states_the_constraints_exclude() {
        let body = format!("{SPEC}\nBelow == x < 2\nStep == x' - x = 1");
        let config = "SPECIFICATION Spec\nCONSTRAINT Below";
        let outcome = run(&body, config, System { init: vec![0], next: counter });
        // State 2 is generated but neither stored nor expanded, so nothing deadlocks.
        assert_eq!(counts(&outcome), (Status::Success, Some(3), Some(2), Some(2)));
        let outcome = run(
            &body,
            "SPECIFICATION Spec\nACTION_CONSTRAINT Step\nCONSTRAINT Below",
            System { init: vec![0], next: |x| vec![x + 2, x + 1] },
        );
        assert_eq!(counts(&outcome), (Status::Success, Some(5), Some(2), Some(2)));
    }

    #[test]
    fn checks_implied_actions_and_initial_predicates() {
        let body = format!("{SPEC}\nUp == [][x' > x]_x\nStart == x = 0\nAlways == []Start");
        let config = "SPECIFICATION Spec\nPROPERTY Up\nCHECK_DEADLOCK FALSE";
        let outcome = run(&body, config, System { init: vec![0], next: |x| vec![(x + 1) % 3] });
        assert_eq!(outcome.status, Status::LivenessViolation);
        assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Up"), Some(4)));
        let config = "SPECIFICATION Spec\nPROPERTY Start\nCHECK_DEADLOCK FALSE";
        let outcome = run(&body, config, System { init: vec![1], next: counter });
        assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Start"), Some(1)));
        // []P of a state predicate is an invariant, named by P.
        let config = "SPECIFICATION Spec\nPROPERTY Always\nCHECK_DEADLOCK FALSE";
        let outcome = run(&body, config, System { init: vec![0], next: counter });
        assert_eq!(outcome.status, Status::InvariantViolation);
        assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Start"), Some(2)));
    }

    #[test]
    fn answers_tlcget_like_tlc() {
        let body =
            format!("{SPEC}\nShallow == TLCGet(\"level\") < 3\nFew == TLCGet(\"distinct\") < 3");
        let config = "SPECIFICATION Spec\nINVARIANT Shallow\nCHECK_DEADLOCK FALSE";
        let outcome = run(&body, config, System { init: vec![0], next: counter });
        assert_eq!(
            (outcome.violation.as_deref(), outcome.trace_length),
            (Some("Shallow"), Some(3))
        );
        let config = "SPECIFICATION Spec\nINVARIANT Few\nCHECK_DEADLOCK FALSE";
        let outcome = run(&body, config, System { init: vec![0], next: counter });
        assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Few"), Some(4)));
    }
}
