//! The breadth-first search with several workers, as tla-ts `parallel.ts` does it: the workers
//! expand one level of the state graph at a time, taking states from the level in chunks, and
//! share a set of fingerprints split into shards. Each distinct state is expanded once, so the
//! states generated, the distinct states, and the depth are those of the search with one
//! worker.
//!
//! Under a `VIEW` or a `SYMMETRY`, states that differ share a fingerprint, and which of them the
//! search keeps decides the successors it finds when the spec isn't symmetric, as with a `CHOOSE`
//! over the symmetric set. So of the successors in a level that share a fingerprint, a worker
//! keeps the one the search with one worker finds first: the first successor of the first state
//! in the level's order. It checks the invariants of that one, and the level after keeps that
//! order, so the search finds the states that search does.
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
use crate::progress::{Counts, Event, Progress, Ticker};
use crate::report::OUT_DEGREE_BUCKETS;

/// How many shards the set of fingerprints has, a power of two.
const SHARDS: usize = 256;

/// How many states a worker takes from the level at a time.
const CHUNK: usize = 16;

/// The stack of each worker, as large as the search with one worker gets.
const STACK: usize = 1 << 30;

/// Where the search with one worker finds a successor: the index in the level of the state it
/// expands, and the successor's place among those of that state.
type Key = (u64, u32);

/// A successor found in the level being expanded, the first with its fingerprint so far.
struct Candidate {
    fingerprint: u128,
    key: Key,
    state: State,
}

/// One shard of the fingerprints: those of the levels expanded, and the successors found in the
/// level being expanded.
#[derive(Default)]
struct Shard {
    seen: HashTable<u128>,
    level: HashTable<Candidate>,
}

/// The fingerprints of the states found, in shards each with its own lock.
struct Seen {
    shards: Vec<Mutex<Shard>>,
}

impl Seen {
    fn new() -> Self {
        Self { shards: (0..SHARDS).map(|_| Mutex::new(Shard::default())).collect() }
    }

    fn shard(&self, fingerprint: u128) -> &Mutex<Shard> {
        &self.shards[(fingerprint >> 64) as usize & (SHARDS - 1)]
    }

    fn contains(&self, fingerprint: u128) -> bool {
        let shard = self.shard(fingerprint).lock().unwrap();
        shard.seen.find(fingerprint as u64, |&found| found == fingerprint).is_some()
    }

    /// Adds `fingerprint`, and returns whether it is new.
    fn insert(&self, fingerprint: u128) -> bool {
        let mut shard = self.shard(fingerprint).lock().unwrap();
        if shard.seen.find(fingerprint as u64, |&found| found == fingerprint).is_some() {
            return false;
        }
        shard.seen.insert_unique(fingerprint as u64, fingerprint, |&found| found as u64);
        true
    }

    /// Offers a successor found in the level being expanded: it stays unless a level before has
    /// its fingerprint, or a successor found before it in the order of the search with one
    /// worker has.
    fn offer(&self, fingerprint: u128, key: Key, state: &State) {
        let mut shard = self.shard(fingerprint).lock().unwrap();
        let shard = &mut *shard;
        if shard.seen.find(fingerprint as u64, |&found| found == fingerprint).is_some() {
            return;
        }
        match shard.level.find_mut(fingerprint as u64, |found| found.fingerprint == fingerprint) {
            Some(found) if found.key <= key => {}
            Some(found) => {
                found.key = key;
                found.state = state.clone();
            }
            None => {
                let candidate = Candidate { fingerprint, key, state: state.clone() };
                shard
                    .level
                    .insert_unique(fingerprint as u64, candidate, |found| found.fingerprint as u64);
            }
        }
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
    /// The next shard to settle.
    settled: AtomicUsize,
    /// Set when a worker meets what the search with one worker must report.
    stopped: AtomicBool,
}

/// The new states one worker settled in a level, with where they were found.
type Settled = Vec<(Key, State)>;

/// Searches with `workers` workers. Gives up when the model has a violation, a deadlock, or
/// an error, which the search with one worker reports, with whether it reported the initial
/// states computed.
pub fn search<S: Successors + Sync + ?Sized>(
    successors: &S,
    evaluator: &Evaluator,
    plan: &Plan,
    fingerprinter: &Fingerprinter,
    check_deadlock: bool,
    workers: usize,
    progress: &Progress,
) -> Result<Search, bool> {
    progress.report(Event::InitialStatesStarted);
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
        return Err(false);
    }
    let mut distinct = initial.len() as u64;
    progress.report(Event::InitialStatesComputed { generated, distinct });
    let mut depth: u64 = if generated == 0 { 0 } else { 1 };
    let mut out_degrees = vec![0; OUT_DEGREE_BUCKETS];
    let Some(next) = plan.next else {
        return match initial.is_empty() {
            true => Ok(success(evaluator, generated, distinct, depth, out_degrees)),
            false => Err(true),
        };
    };
    let mut ticker = Ticker::new();
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
            settled: AtomicUsize::new(0),
            stopped: AtomicBool::new(false),
        };
        let found: Vec<u64> = level.run(workers, || 0, |generated| level.expand(next, generated));
        if level.stopped.load(Ordering::Relaxed) {
            return Err(true);
        }
        generated += found.iter().sum::<u64>();
        let settled: Vec<Settled> =
            level.run(workers, Settled::new, |settled| level.settle(settled));
        if level.stopped.load(Ordering::Relaxed) {
            return Err(true);
        }
        let mut next_states: Settled = settled.into_iter().flatten().collect();
        // The order the search with one worker finds them in.
        next_states.sort_unstable_by_key(|(key, _)| *key);
        count_out_degrees(&mut out_degrees, states.len(), &next_states);
        states = next_states.into_iter().map(|(_, state)| state).collect();
        distinct += states.len() as u64;
        if !states.is_empty() {
            depth += 1;
        }
        // TLC reports every minute; the workers report between levels.
        if progress.is_reported() && ticker.is_due() {
            let queue = states.len() as u64;
            progress.report(Event::Progress(Counts { generated, distinct, queue, depth }));
        }
    }
    Ok(success(evaluator, generated, distinct, depth, out_degrees))
}

impl<S: Successors + Sync + ?Sized> Level<'_, S> {
    /// Runs `work` on `workers` workers, each with its own result, which a worker that panics
    /// leaves as `start` gives it.
    fn run<T: Send>(
        &self,
        workers: usize,
        start: impl Fn() -> T + Sync,
        work: impl Fn(&mut T) + Sync,
    ) -> Vec<T> {
        std::thread::scope(|scope| {
            let handles: Vec<_> = (0..workers)
                .map(|_| {
                    std::thread::Builder::new()
                        .stack_size(STACK)
                        .spawn_scoped(scope, || {
                            let mut result = start();
                            work(&mut result);
                            result
                        })
                        .expect("a worker thread starts")
                })
                .collect();
            handles
                .into_iter()
                .map(|handle| {
                    handle.join().unwrap_or_else(|_| {
                        self.stopped.store(true, Ordering::Relaxed);
                        start()
                    })
                })
                .collect()
        })
    }

    /// One worker's share of the level, adding the states it generates to `generated`.
    fn expand(&self, next: tla_resolve::DefId, generated: &mut u64) {
        loop {
            if self.stopped.load(Ordering::Relaxed) {
                return;
            }
            let start = self.taken.fetch_add(CHUNK, Ordering::Relaxed);
            if start >= self.states.len() {
                return;
            }
            let end = (start + CHUNK).min(self.states.len());
            for (index, state) in self.states[start..end].iter().enumerate() {
                match self.expand_state(next, (start + index) as u64, state, generated) {
                    Ok(true) => {}
                    Ok(false) | Err(_) => {
                        self.stopped.store(true, Ordering::Relaxed);
                        return;
                    }
                }
            }
        }
    }

    /// Expands `state`, the one at `index` in the level, as the search with one worker does,
    /// offering its successors in the model. `false` at what that search must report.
    fn expand_state(
        &self,
        next: tla_resolve::DefId,
        index: u64,
        state: &State,
        generated: &mut u64,
    ) -> tla_eval::Result<bool> {
        let (evaluator, plan) = (self.evaluator, self.plan);
        let mut count = 0u64;
        let mut holds = true;
        self.successors.next_states(next, state, &mut |successor| {
            let place = count as u32;
            count += 1;
            let fingerprint =
                self.fingerprinter.fingerprint(evaluator, &successor).map_err(fail)?;
            let is_in_model = all_hold(evaluator, &plan.constraints, &successor, None)?
                && all_hold(evaluator, &plan.action_constraints, state, Some(&successor))?;
            // The search with one worker checks the invariants of a state it doesn't store;
            // those of the states it stores, once the level settles which they are.
            if (!is_in_model && !all_hold(evaluator, &plan.invariants, &successor, None)?)
                || !all_hold(evaluator, &plan.action_properties, state, Some(&successor))?
            {
                holds = false;
                return Ok(false);
            }
            if is_in_model {
                self.seen.offer(fingerprint, (index, place), &successor);
            }
            Ok(!self.stopped.load(Ordering::Relaxed))
        })?;
        *generated += count;
        Ok(holds && !(count == 0 && self.check_deadlock))
    }

    /// One worker's share of settling the level: the successors that stay in the shards it takes
    /// are the new states, whose fingerprints join those of the levels before, and whose
    /// invariants it checks.
    fn settle(&self, settled: &mut Settled) {
        loop {
            if self.stopped.load(Ordering::Relaxed) {
                return;
            }
            let index = self.settled.fetch_add(1, Ordering::Relaxed);
            let Some(shard) = self.seen.shards.get(index) else { return };
            let start = settled.len();
            {
                let mut shard = shard.lock().unwrap();
                let shard = &mut *shard;
                for candidate in shard.level.drain() {
                    let fingerprint = candidate.fingerprint;
                    shard
                        .seen
                        .insert_unique(fingerprint as u64, fingerprint, |&found| found as u64);
                    settled.push((candidate.key, candidate.state));
                }
            }
            for (_, state) in &settled[start..] {
                if !all_hold(self.evaluator, &self.plan.invariants, state, None).unwrap_or(false) {
                    self.stopped.store(true, Ordering::Relaxed);
                    return;
                }
            }
        }
    }
}

/// Adds the out-degrees of the states of a level: how many new states each found, from the new
/// states of the next level in their order.
fn count_out_degrees(out_degrees: &mut [u64], expanded: usize, next: &[(Key, State)]) {
    let mut with_new = 0usize;
    let mut position = 0;
    while position < next.len() {
        let parent = next[position].0.0;
        let run = next[position..].iter().take_while(|((found, _), _)| *found == parent).count();
        out_degrees[run.min(OUT_DEGREE_BUCKETS - 1)] += 1;
        with_new += 1;
        position += run;
    }
    out_degrees[0] += (expanded - with_new) as u64;
}

fn success(
    evaluator: &Evaluator,
    generated: u64,
    distinct: u64,
    depth: u64,
    out_degrees: Vec<u64>,
) -> Search {
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
        actions: Vec::new(),
        loop_start: None,
        loop_action: None,
        violated: Vec::new(),
        generated,
        distinct,
        depth,
        counts: Counts { generated, distinct, queue: 0, depth },
        out_degrees,
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

    /// The states 0 to 63 go to 1000 and up, which share a view, so which of them the search
    /// keeps decides what follows: 1000 + p goes to p + 1 states. The state 0 finds 1000 last
    /// of its successors, after the other states found theirs.
    fn shared_view(x: i32) -> Vec<i32> {
        match x {
            0 => (10_000..12_000).chain([1000]).collect(),
            1..64 => vec![1000 + x],
            1000..2000 => (0..=x - 1000).map(|step| 20_000 + 100 * (x - 1000) + step).collect(),
            _ => Vec::new(),
        }
    }

    #[test]
    fn keeps_the_state_one_worker_finds_first_of_a_view() {
        let body = "View == IF x >= 1000 /\\ x < 2000 THEN 1000 ELSE x\nInit == TRUE\n\
            Next == TRUE\nSpec == Init /\\ [][Next]_x";
        let config = "SPECIFICATION Spec\nVIEW View\nCHECK_DEADLOCK FALSE";
        for _ in 0..10 {
            let found: Vec<_> = [1, 2, 4, 8]
                .into_iter()
                .map(|workers| {
                    let system = System { init: (0..64).collect(), next: shared_view };
                    summary(&run_with_workers(body, config, system, workers))
                })
                .collect();
            // 1000, found from 0, goes to 20000 alone.
            assert_eq!(found[0].2, Some(64 + 2000 + 1 + 1));
            assert!(found.iter().all(|outcome| *outcome == found[0]), "{found:?}");
        }
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
