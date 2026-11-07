//! Breadth-first search of the state graph, as TLC's model checker explores it with one worker:
//! a set of the fingerprints of the states found, a FIFO queue of those to expand, and a link
//! from each state to the one it was found from, for traces. It counts the states generated,
//! repeats and initial states included, and the distinct states, as TLC does.
//!
//! Like TLC, it keeps no state once it has expanded it (`store`), and rebuilds the behavior to
//! a violation from the initial states by the fingerprints along it.

mod live;
pub mod parallel;
mod store;
mod trace;

pub use trace::Steps;

use std::cell::RefCell;
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

use tla_tools_eval::{EvalError, Evaluator, Result, State, Statistics};
use tla_tools_resolve::DefId;
use tla_tools_value::{Symbol, Value};

use crate::fingerprint::Fingerprinter;
use crate::liveness::checker::{Checker, LiveSuccessor};
use crate::plan::{Check, Plan};
use crate::progress::{Counts, Event, Progress, Ticker};
use crate::report::OUT_DEGREE_BUCKETS;
use store::Store;

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

impl Successors for Evaluator {
    fn init_states(
        &self,
        init: &[DefId],
        found: &mut dyn FnMut(State) -> Result<bool>,
    ) -> Result<()> {
        Evaluator::init_states(self, init, found)
    }

    fn next_states(
        &self,
        next: DefId,
        state: &State,
        found: &mut dyn FnMut(State) -> Result<bool>,
    ) -> Result<()> {
        Evaluator::next_states(self, next, state, found)
    }
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
    /// Liveness checking found a behavior that violates the temporal properties.
    LivenessViolation,
    /// Liveness checking found a behavior that violates the temporal properties as it added a
    /// state to the behavior graph, which TLC reports as a violated property.
    TemporalViolation,
    /// Evaluation failed.
    Error(String),
}

/// The result of a search: how it ended, the behavior that ends in the violation, and TLC's
/// counts.
#[derive(Clone, Debug)]
pub struct Search {
    pub ending: Ending,
    /// The number of states in the behavior that ends in the violation.
    pub trace_length: usize,
    /// That behavior, rebuilt from the initial states, as far as it could be.
    pub trace: Vec<State>,
    /// The action of each step of the trace and of the step back for a lasso, and what the spec
    /// printed as TLC computed them again.
    pub steps: Steps,
    /// For a lasso, the index of the state the trace loops back to.
    pub loop_start: Option<usize>,
    /// How many states of the trace TLC computes again before it prints the behavior, which
    /// puts what the spec prints computing them before the behavior's heading.
    pub printed_before: usize,
    /// The names of the temporal properties a liveness counterexample violates.
    pub violated: Vec<String>,
    pub generated: u64,
    pub distinct: u64,
    pub depth: u64,
    /// The counts as TLC reports them once the search ends.
    pub counts: Counts,
    /// How many expanded states had each number of new successors.
    pub out_degrees: Vec<u64>,
}

/// What `TLCGet("level")` reads: the state the model checker expands, with its index, and the
/// one it checks.
#[derive(Default)]
struct Cursor {
    expanding: Option<(State, i32, usize)>,
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
            Some((expanding, level, _)) if Arc::ptr_eq(expanding, state) => *level,
            Some((_, level, _)) => level + 1,
            None => 0,
        }
    }
}

/// The behavior to a violation.
enum Trail {
    /// The behavior through the stored state `stored`, if any, to `last`, a state that wasn't
    /// stored, if any.
    Search { stored: Option<usize>, last: Option<State> },
    /// A behavior the liveness checker found, by state index, which loops back to the state at
    /// `cycle_start` unless that is its length.
    Live { states: Vec<u32>, cycle_start: usize },
}

impl Trail {
    fn at(stored: Option<usize>, last: Option<State>) -> Self {
        Trail::Search { stored, last }
    }
}

struct Explorer<'a, S: Successors + ?Sized> {
    successors: &'a S,
    evaluator: &'a Evaluator,
    plan: &'a Plan,
    fingerprinter: &'a Fingerprinter,
    check_deadlock: bool,
    /// The index of each variable in a state, in TLC's order of the variables.
    tlc_order: &'a [usize],
    store: Arc<Mutex<Store>>,
    /// The states to expand, in the order they were found.
    queue: VecDeque<State>,
    cursor: Arc<Mutex<Cursor>>,
    generated: u64,
    initial: u64,
    depth: u32,
    /// The index of the state being expanded, once the initial states are done.
    expanding: Option<usize>,
    liveness: Option<RefCell<Checker<'a>>>,
    /// The successors in the model of the state being expanded, for the liveness checker.
    live_successors: Vec<LiveSuccessor>,
    progress: &'a Progress,
    ticker: Ticker,
    /// The new successors of the state being expanded, and how many states had each number.
    new_successors: u64,
    out_degrees: Vec<u64>,
}

/// What a visit to a state found.
enum Visit {
    Continue,
    Stop(Ending, Trail),
}

/// Explores the states of `plan` breadth first.
#[allow(clippy::too_many_arguments)]
pub fn search<S: Successors + ?Sized>(
    successors: &S,
    evaluator: &Evaluator,
    plan: &Plan,
    fingerprinter: &Fingerprinter,
    check_deadlock: bool,
    tlc_order: &[usize],
    liveness: Option<Checker<'_>>,
    progress: &Progress,
) -> Search {
    // Only `TLCExt!Trace` reads the behavior to a state while the search runs.
    let reads_behaviors =
        evaluator.spec().modules.iter().any(|module| module.name.as_str() == "TLCExt");
    let store = Arc::new(Mutex::new(Store::new(reads_behaviors)));
    let cursor = Arc::new(Mutex::new(Cursor::default()));
    let runtime = evaluator.runtime();
    let level = cursor.clone();
    runtime.on_level(move |state| level.lock().unwrap().level(state));
    if reads_behaviors {
        let behavior_store = store.clone();
        let behavior_cursor = cursor.clone();
        runtime.on_behavior(move |state| {
            // A state being checked follows the one being expanded.
            let expanding = behavior_cursor.lock().unwrap().expanding.clone();
            let Some((expanding, _, index)) = expanding else { return vec![state.clone()] };
            let mut path = behavior_store.lock().unwrap().path(index).unwrap_or_default();
            if !Arc::ptr_eq(&expanding, state) {
                path.push(state.clone());
            }
            path
        });
    }
    let mut explorer = Explorer {
        successors,
        evaluator,
        plan,
        fingerprinter,
        check_deadlock,
        tlc_order,
        store,
        queue: VecDeque::new(),
        cursor,
        generated: 0,
        initial: 0,
        depth: 0,
        expanding: None,
        liveness: liveness.map(RefCell::new),
        live_successors: Vec::new(),
        progress,
        ticker: Ticker::new(),
        new_successors: 0,
        out_degrees: vec![0; OUT_DEGREE_BUCKETS],
    };
    let (ending, trail) = explorer.run();
    // The states stored on the way to the violation, the last of them the one it was found from.
    let stored = match &trail {
        Some(Trail::Search { stored: Some(index), .. }) => {
            explorer.store.lock().unwrap().depth(*index) as usize
        }
        _ => 0,
    };
    let trace_length = match &trail {
        Some(Trail::Search { last, .. }) => stored + usize::from(last.is_some()),
        // TLC numbers the stuttering step at the end of a lasso like a state.
        Some(Trail::Live { states, cycle_start }) => {
            states.len() + usize::from(states.len().checked_sub(*cycle_start) == Some(1))
        }
        None => 0,
    };
    // TLC's `printTrace` computes again the stored states before the last one, and then prints
    // the behavior, computing the last stored state and the violating successor again as it
    // prints them. It computes the initial state only when another stored state follows it.
    // It computes a liveness counterexample again as it prints it.
    let (computes_initial, printed_before) = match &trail {
        Some(Trail::Search { .. }) => (stored >= 2, stored.saturating_sub(1)),
        _ => (true, 0),
    };
    let loop_start = match &trail {
        Some(Trail::Live { states, cycle_start }) => {
            Some(*cycle_start).filter(|start| *start < states.len())
        }
        _ => None,
    };
    // What the spec prints finding the behavior again isn't what TLC prints.
    let runtime = explorer.evaluator.runtime();
    let trace = runtime.capture(|| trail.map(|trail| explorer.behavior(trail))).0;
    let trace = trace.unwrap_or_default();
    let steps = explorer.steps(&trace, loop_start, computes_initial);
    let violated = match (&ending, &explorer.liveness) {
        (Ending::LivenessViolation | Ending::TemporalViolation, Some(liveness)) => {
            let cycle_start = loop_start.unwrap_or(trace.len().saturating_sub(1));
            liveness.borrow().violated_properties(&trace, cycle_start)
        }
        _ => Vec::new(),
    };
    let distinct = explorer.store.lock().unwrap().len() as u64;
    Search {
        ending,
        trace_length,
        trace,
        steps,
        loop_start,
        printed_before,
        violated,
        generated: explorer.generated,
        distinct,
        depth: if explorer.generated == 0 { 0 } else { u64::from(explorer.depth.max(1)) },
        counts: explorer.counts(),
        out_degrees: explorer.out_degrees,
    }
}

impl<S: Successors + ?Sized> Explorer<'_, S> {
    fn run(&mut self) -> (Ending, Option<Trail>) {
        self.progress.report(Event::InitialStatesStarted);
        let mut stopped = None;
        let (successors, init) = (self.successors, &self.plan.init);
        let result = successors.init_states(init, &mut |state| match self.visit_initial(state)? {
            Visit::Continue => Ok(true),
            Visit::Stop(ending, trail) => {
                stopped = Some((ending, Some(trail)));
                Ok(false)
            }
        });
        self.cursor.lock().unwrap().candidate = None;
        if let Err(error) = result {
            return (Ending::Error(error.to_string()), None);
        }
        if let Some(stopped) = stopped {
            return stopped;
        }
        let distinct = self.store.lock().unwrap().len() as u64;
        self.progress.report(Event::InitialStatesComputed { generated: self.initial, distinct });
        let Some(next) = self.plan.next else {
            if self.queue.is_empty() {
                return (Ending::Success, None);
            }
            let message = "No next state actions defined to generate successor states from.";
            return (Ending::Error(message.into()), None);
        };
        let mut index = 0;
        loop {
            if self.evaluator.runtime().is_stopped.load(std::sync::atomic::Ordering::Relaxed) {
                break;
            }
            let Some(state) = self.queue.pop_front() else { break };
            let depth = self.store.lock().unwrap().depth(index);
            self.cursor.lock().unwrap().expanding = Some((state.clone(), depth as i32, index));
            self.expanding = Some(index);
            self.update_statistics(None);
            if self.progress.is_reported() && self.ticker.is_due() {
                self.progress.report(Event::Progress(self.counts()));
            }
            self.new_successors = 0;
            // TLC seeds a worker's random choices with the fingerprint of the state it expands.
            self.evaluator.runtime().set_expanding(Some(state.clone()));
            let mut count = 0u64;
            let mut stopped = None;
            let successors = self.successors;
            let result = successors.next_states(next, &state, &mut |successor| {
                count += 1;
                match self.visit_successor(index, &state, depth, successor)? {
                    Visit::Continue => Ok(true),
                    Visit::Stop(ending, trail) => {
                        stopped = Some((ending, Some(trail)));
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
            let at_state = || Some(Trail::at(Some(index), None));
            if let Err(error) = result {
                return (Ending::Error(error.to_string()), at_state());
            }
            if let Some(stopped) = stopped {
                return stopped;
            }
            if count == 0 && self.check_deadlock {
                return (Ending::Deadlock, at_state());
            }
            self.out_degrees[(self.new_successors as usize).min(OUT_DEGREE_BUCKETS - 1)] += 1;
            let live = std::mem::take(&mut self.live_successors);
            if let Some(ending) = self.add_live_state(index, &state, depth, &live) {
                return ending;
            }
            index += 1;
        }
        // The postconditions read the counts of the whole search.
        self.expanding = Some(self.store.lock().unwrap().len());
        self.update_statistics(None);
        // TLC checks the temporal properties on the whole graph, with -lncheck final.
        if let Some(liveness) = &self.liveness {
            let branches = liveness.borrow().branches();
            let states = self.store.lock().unwrap().len() as u64;
            self.progress.report(Event::LivenessStarted {
                counts: self.counts(),
                branches,
                states,
            });
        }
        if let Some(ending) = self.find_live_violation() {
            return ending;
        }
        (Ending::Success, None)
    }

    /// The behavior that ends in `trail`, rebuilt as TLC rebuilds it: from the initial states,
    /// each step to the successor with the fingerprint stored for the next state along it.
    fn behavior(&self, trail: Trail) -> Vec<State> {
        let (stored, last) = match trail {
            Trail::Search { stored, last } => (stored, last),
            Trail::Live { states, .. } => {
                let store = self.store.lock().unwrap();
                let fingerprints: Vec<u128> =
                    states.iter().map(|&index| store.fingerprint(index as usize)).collect();
                drop(store);
                return self.replay(&fingerprints);
            }
        };
        let mut behavior = Vec::new();
        if let Some(stored) = stored {
            let store = self.store.lock().unwrap();
            behavior = match store.path(stored) {
                Some(path) => path,
                None => {
                    let fingerprints: Vec<u128> = store
                        .lineage(stored)
                        .into_iter()
                        .map(|index| store.fingerprint(index))
                        .collect();
                    drop(store);
                    self.replay(&fingerprints)
                }
            };
        }
        behavior.extend(last);
        behavior
    }

    /// The states with these fingerprints, each a successor of the one before, as far as they
    /// can be found again.
    fn replay(&self, fingerprints: &[u128]) -> Vec<State> {
        let mut behavior: Vec<State> = Vec::new();
        for &fingerprint in fingerprints {
            // A behavior may stay in a state, as a lasso's cycle does.
            if let Some(previous) = behavior.last()
                && self.fingerprint(previous).is_ok_and(|found| found == fingerprint)
            {
                behavior.push(previous.clone());
                continue;
            }
            match self.find_again(behavior.last(), fingerprint) {
                Some(state) => behavior.push(state),
                None => break,
            }
        }
        behavior
    }

    /// The initial state, or the successor of `previous`, with the fingerprint `wanted`.
    fn find_again(&self, previous: Option<&State>, wanted: u128) -> Option<State> {
        let mut found = None;
        let mut matches = |state: State| {
            if self.fingerprint(&state).is_ok_and(|fingerprint| fingerprint == wanted) {
                found = Some(state);
                return Ok(false);
            }
            Ok(true)
        };
        let result = match previous {
            None => self.successors.init_states(&self.plan.init, &mut matches),
            Some(state) => {
                let next = self.plan.next?;
                self.evaluator.runtime().set_expanding(Some(state.clone()));
                let result = self.successors.next_states(next, state, &mut matches);
                self.evaluator.runtime().set_expanding(None);
                result
            }
        };
        result.ok().and(found)
    }

    /// The counts `update_statistics` last published, with the states queued to expand.
    fn counts(&self) -> Counts {
        let statistics = self.evaluator.runtime().statistics().unwrap_or_default();
        let count = |count: i64| count.max(0) as u64;
        // TLC reports a depth of 0 until it generates a state.
        let depth = if self.generated == 0 { 0 } else { count(statistics.diameter) };
        Counts {
            generated: count(statistics.generated),
            distinct: count(statistics.distinct),
            queue: self.queue.len() as u64,
            depth,
        }
    }

    /// Publishes the counts `TLCGet` reads, as TLC keeps them while it explores: a state is
    /// generated as soon as it is found, and distinct once it is found new, before its
    /// invariants are checked. `pending` is the depth of a new state not stored yet.
    fn update_statistics(&self, pending: Option<u32>) {
        let stored = self.store.lock().unwrap().len() as i64;
        let distinct = stored + i64::from(pending.is_some());
        let queue = match self.expanding {
            Some(expanding) => (stored - expanding as i64 - 1).max(0),
            // TLC queues a new initial state before it checks it.
            None => distinct,
        };
        let diameter = i64::from(self.depth.max(pending.unwrap_or(0)));
        let (generated, initial) = (self.generated as i64, self.initial as i64);
        self.evaluator.runtime().update_statistics(|statistics: &mut Statistics| {
            statistics.generated = generated;
            statistics.distinct = distinct;
            statistics.initial = initial;
            statistics.queue = queue;
            statistics.diameter = diameter;
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
            incomplete: None,
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

    /// Counts the `_POSSIBLE` predicates that `state`, or the step to `next`, witnesses, in the
    /// counts `_Possible!_Counts` reads.
    fn track_possible(&self, checks: &[Check], state: &State, next: Option<&State>) -> Result<()> {
        for check in checks {
            let is_witnessed = self.holds(check, state, next)?;
            let mut registers = self.evaluator.runtime().registers.lock().unwrap();
            let count = registers.possible.entry(Symbol::intern(&check.name)).or_insert(0);
            *count += i32::from(is_witnessed);
        }
        Ok(())
    }

    fn fingerprint(&self, state: &State) -> Result<u128> {
        self.fingerprinter.fingerprint(self.evaluator, state).map_err(|message| EvalError {
            message,
            module: Symbol::intern(""),
            span: Default::default(),
            line: 0,
            column: 0,
            incomplete: None,
        })
    }

    fn store(&mut self, fingerprint: u128, state: State, parent: Option<usize>, depth: u32) {
        self.depth = self.depth.max(depth);
        self.new_successors += u64::from(parent.is_some());
        self.store.lock().unwrap().insert(fingerprint, &state, parent, depth);
        self.queue.push_back(state);
    }

    fn is_found(&self, fingerprint: u128) -> bool {
        self.store.lock().unwrap().contains(fingerprint)
    }

    /// TLC's `ModelChecker.checkInitialState` with one worker.
    fn visit_initial(&mut self, state: State) -> Result<Visit> {
        self.generated += 1;
        self.initial += 1;
        self.update_statistics(None);
        self.cursor.lock().unwrap().candidate = Some((state.clone(), 1));
        let fingerprint = self.fingerprint(&state)?;
        let is_in_model = self.all_hold(&self.plan.constraints, &state, None)?;
        if is_in_model {
            self.track_possible(&self.plan.possible, &state, None)?;
        }
        if is_in_model && self.is_found(fingerprint) {
            return Ok(Visit::Continue);
        }
        if is_in_model {
            self.update_statistics(Some(1));
            self.add_live_initial_state(&state)?;
        }
        let trail = |state: &State| Trail::at(None, Some(state.clone()));
        if let Some(check) = self.first_failing(&self.plan.invariants, &state, None)? {
            let ending = Ending::InvariantViolation(check.name.clone());
            return Ok(Visit::Stop(ending, trail(&state)));
        }
        if let Some(check) = self.first_failing(&self.plan.initial_predicates, &state, None)? {
            let ending = Ending::PropertyViolation(check.name.clone());
            return Ok(Visit::Stop(ending, trail(&state)));
        }
        if is_in_model {
            self.store(fingerprint, state, None, 1);
        }
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
        self.update_statistics(None);
        self.cursor.lock().unwrap().candidate = Some((successor.clone(), depth as i32 + 1));
        let fingerprint = self.fingerprint(&successor)?;
        let found = self.store.lock().unwrap().find(fingerprint);
        let is_found = found.is_some();
        let is_state_in_model = self.all_hold(&self.plan.constraints, &successor, None)?;
        if is_state_in_model {
            self.track_possible(&self.plan.possible, &successor, None)?;
        }
        let is_in_model = is_state_in_model
            && self.all_hold(&self.plan.action_constraints, state, Some(&successor))?;
        if is_in_model {
            self.track_possible(&self.plan.action_possible, state, Some(&successor))?;
        }
        let is_new = is_in_model && !is_found;
        if self.liveness.is_some() && is_in_model {
            let index = found.unwrap_or_else(|| self.store.lock().unwrap().len()) as u32;
            self.live_successors
                .push(LiveSuccessor { index: Some(index), state: successor.clone() });
        }
        if is_new {
            self.update_statistics(Some(depth + 1));
        }
        let trace = || Trail::at(Some(parent), Some(successor.clone()));
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
mod tests;
