//! The breadth-first search with several workers, as tla-ts `parallel.ts` does it: the workers
//! expand one level of the state graph at a time, taking states from the level in chunks, and
//! share a set of fingerprints split into shards. Each distinct state is expanded once, so the
//! states generated, the distinct states, and the depth are those of the search with one
//! worker.
//!
//! It only finds that a model holds. At a violation, a deadlock, or an error, it gives up, and
//! the search with one worker runs instead, which finds what TLC reports with `-workers 1`: the
//! first violation in TLC's order and the shortest behavior to it.

use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use hashbrown::HashTable;
use tla_eval::{Evaluator, State, Statistics};

use super::{Ending, Search, Successors};
use crate::fingerprint::Fingerprinter;
use crate::plan::{Check, Plan};

/// How many shards the set of fingerprints has, a power of two.
const SHARDS: usize = 256;

/// How many states a worker takes from the level at a time.
const CHUNK: usize = 16;

/// The stack of each worker, as large as the search with one worker gets.
const STACK: usize = 1 << 30;

/// The fingerprints of the states found, in shards each with its own lock.
struct Seen {
    shards: Vec<Mutex<HashTable<u128>>>,
}

impl Seen {
    fn new() -> Self {
        Self { shards: (0..SHARDS).map(|_| Mutex::new(HashTable::new())).collect() }
    }

    fn shard(&self, fingerprint: u128) -> &Mutex<HashTable<u128>> {
        &self.shards[(fingerprint >> 64) as usize & (SHARDS - 1)]
    }

    fn contains(&self, fingerprint: u128) -> bool {
        let shard = self.shard(fingerprint).lock().unwrap();
        shard.find(fingerprint as u64, |&found| found == fingerprint).is_some()
    }

    /// Adds `fingerprint`, and returns whether it is new.
    fn insert(&self, fingerprint: u128) -> bool {
        let mut shard = self.shard(fingerprint).lock().unwrap();
        if shard.find(fingerprint as u64, |&found| found == fingerprint).is_some() {
            return false;
        }
        shard.insert_unique(fingerprint as u64, fingerprint, |&found| found as u64);
        true
    }
}

/// What the workers share while they expand a level.
struct Level<'a, S: Successors + Sync + ?Sized> {
    successors: &'a S,
    evaluator: &'a Evaluator,
    plan: &'a Plan,
    fingerprinter: &'a Fingerprinter,
    check_deadlock: bool,
    seen: &'a Seen,
    states: &'a [State],
    taken: AtomicUsize,
    /// Set when a worker meets what the search with one worker must report.
    stopped: AtomicBool,
}

/// What one worker found in a level.
#[derive(Default)]
struct Found {
    next: Vec<State>,
    generated: u64,
}

/// Searches with `workers` workers. `None` when the model has a violation, a deadlock, or an
/// error, which the search with one worker reports.
pub fn search<S: Successors + Sync + ?Sized>(
    successors: &S,
    evaluator: &Evaluator,
    plan: &Plan,
    fingerprinter: &Fingerprinter,
    check_deadlock: bool,
    workers: usize,
) -> Option<Search> {
    let seen = Seen::new();
    let mut generated: u64 = 0;
    let mut initial: Vec<State> = Vec::new();
    let mut stopped = false;
    let result = successors.init_states(&plan.init, &mut |state| {
        generated += 1;
        let fingerprint = fingerprinter.fingerprint(evaluator, &state).map_err(fail)?;
        let is_in_model = all_hold(evaluator, &plan.constraints, &state, None)?;
        if is_in_model && seen.contains(fingerprint) {
            return Ok(true);
        }
        if !all_hold(evaluator, &plan.invariants, &state, None)?
            || !all_hold(evaluator, &plan.initial_predicates, &state, None)?
        {
            stopped = true;
            return Ok(false);
        }
        if is_in_model && seen.insert(fingerprint) {
            initial.push(state);
        }
        Ok(true)
    });
    if result.is_err() || stopped {
        return None;
    }
    let mut distinct = initial.len() as u64;
    let mut depth: u64 = if generated == 0 { 0 } else { 1 };
    let Some(next) = plan.next else {
        return initial.is_empty().then(|| success(evaluator, generated, distinct, depth));
    };
    let mut states = initial;
    while !states.is_empty() {
        let level = Level {
            successors,
            evaluator,
            plan,
            fingerprinter,
            check_deadlock,
            seen: &seen,
            states: &states,
            taken: AtomicUsize::new(0),
            stopped: AtomicBool::new(false),
        };
        let found: Vec<Found> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..workers)
                .map(|_| {
                    std::thread::Builder::new()
                        .stack_size(STACK)
                        .spawn_scoped(scope, || level.expand(next))
                        .expect("a worker thread starts")
                })
                .collect();
            handles.into_iter().map(|handle| handle.join().unwrap_or_default()).collect()
        });
        if level.stopped.load(Ordering::Relaxed) {
            return None;
        }
        generated += found.iter().map(|found| found.generated).sum::<u64>();
        states = found.into_iter().flat_map(|found| found.next).collect();
        distinct += states.len() as u64;
        if !states.is_empty() {
            depth += 1;
        }
    }
    Some(success(evaluator, generated, distinct, depth))
}

impl<S: Successors + Sync + ?Sized> Level<'_, S> {
    /// One worker's share of the level.
    fn expand(&self, next: tla_resolve::DefId) -> Found {
        let mut found = Found::default();
        loop {
            if self.stopped.load(Ordering::Relaxed) {
                return found;
            }
            let start = self.taken.fetch_add(CHUNK, Ordering::Relaxed);
            if start >= self.states.len() {
                return found;
            }
            let end = (start + CHUNK).min(self.states.len());
            for state in &self.states[start..end] {
                match self.expand_state(next, state, &mut found) {
                    Ok(true) => {}
                    Ok(false) | Err(_) => {
                        self.stopped.store(true, Ordering::Relaxed);
                        return found;
                    }
                }
            }
        }
    }

    /// Expands `state`, as the search with one worker does. `false` at what that search must
    /// report.
    fn expand_state(
        &self,
        next: tla_resolve::DefId,
        state: &State,
        found: &mut Found,
    ) -> tla_eval::Result<bool> {
        let (evaluator, plan) = (self.evaluator, self.plan);
        let mut count = 0u64;
        let mut holds = true;
        self.successors.next_states(next, state, &mut |successor| {
            count += 1;
            let fingerprint =
                self.fingerprinter.fingerprint(evaluator, &successor).map_err(fail)?;
            let is_in_model = all_hold(evaluator, &plan.constraints, &successor, None)?
                && all_hold(evaluator, &plan.action_constraints, state, Some(&successor))?;
            let is_new = is_in_model && self.seen.insert(fingerprint);
            // The search with one worker checks the invariants of a state it hasn't stored.
            let is_checked = is_new || !is_in_model;
            if (is_checked && !all_hold(evaluator, &plan.invariants, &successor, None)?)
                || !all_hold(evaluator, &plan.action_properties, state, Some(&successor))?
            {
                holds = false;
                return Ok(false);
            }
            if is_new {
                found.next.push(successor);
            }
            Ok(!self.stopped.load(Ordering::Relaxed))
        })?;
        found.generated += count;
        Ok(holds && !(count == 0 && self.check_deadlock))
    }
}

fn success(evaluator: &Evaluator, generated: u64, distinct: u64, depth: u64) -> Search {
    evaluator.runtime().update_statistics(|statistics: &mut Statistics| {
        statistics.generated = generated as i64;
        statistics.distinct = distinct as i64;
        statistics.queue = 0;
        statistics.diameter = depth as i64;
    });
    Search {
        ending: Ending::Success,
        trace_length: 0,
        trace: Vec::new(),
        generated,
        distinct,
        depth,
    }
}

fn fail(message: String) -> tla_eval::EvalError {
    tla_eval::EvalError {
        message,
        module: tla_value::Symbol::intern(""),
        span: Default::default(),
        line: 0,
        column: 0,
        incomplete: None,
    }
}

/// Whether every check holds. A check that isn't a boolean fails, as the search with one worker
/// reports.
fn all_hold(
    evaluator: &Evaluator,
    checks: &[Check],
    state: &State,
    next: Option<&State>,
) -> tla_eval::Result<bool> {
    for check in checks {
        let value = match next {
            Some(next) => evaluator.eval_action(check.def, state, next)?,
            None => evaluator.eval_def(check.def, Some(state))?,
        };
        match value.as_bool() {
            Some(true) => {}
            Some(false) => return Ok(false),
            None => return Err(fail(format!("{} is not a boolean", check.name))),
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use crate::Status;
    use crate::testing::{System, run_with_workers};

    const SPEC: &str = "Init == x \\in {0, 1}\nNext == x' = x + 1\nSpec == Init /\\ [][Next]_x\n\
        Small == x < 40\nPrinted == x < 40 /\\ Print(x, TRUE)";

    /// Each state goes to the next three, up to 50.
    fn fan(x: i32) -> Vec<i32> {
        (1..=3).map(|step| x + step).filter(|&next| next <= 50).collect()
    }

    fn outcomes(body_config: (&str, &str)) -> Vec<crate::Outcome> {
        let (body, config) = body_config;
        [1, 2, 4, 8]
            .into_iter()
            .map(|workers| {
                run_with_workers(body, config, System { init: vec![0, 1], next: fan }, workers)
            })
            .collect()
    }

    fn summary(
        outcome: &crate::Outcome,
    ) -> (Status, Option<u64>, Option<u64>, Option<u64>, Option<usize>) {
        (outcome.status, outcome.generated, outcome.distinct, outcome.depth, outcome.trace_length)
    }

    #[test]
    fn counts_as_one_worker_does() {
        let found = outcomes((SPEC, "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE"));
        assert_eq!(summary(&found[0]), (Status::Success, Some(149), Some(51), Some(18), None));
        assert!(found.iter().all(|outcome| summary(outcome) == summary(&found[0])));
    }

    #[test]
    fn leaves_violations_and_effects_to_one_worker() {
        // The shortest behavior to the violation, as one worker finds it.
        let found = outcomes((SPEC, "SPECIFICATION Spec\nINVARIANT Small\nCHECK_DEADLOCK FALSE"));
        assert_eq!(found[0].trace_length, Some(14));
        assert!(found.iter().all(|outcome| summary(outcome) == summary(&found[0])));
        // A deadlock at 50.
        let found = outcomes((SPEC, "SPECIFICATION Spec"));
        assert_eq!(found[0].status, Status::Deadlock);
        assert!(found.iter().all(|outcome| summary(outcome) == summary(&found[0])));
        // Printing is an effect another order could show.
        let found = outcomes((SPEC, "SPECIFICATION Spec\nINVARIANT Printed\nCHECK_DEADLOCK FALSE"));
        assert!(found.iter().all(|outcome| summary(outcome) == summary(&found[0])));
    }
}
