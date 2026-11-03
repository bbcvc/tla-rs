//! What TLC's operators with effects use: printed output, the registers of `TLCSet` and
//! `TLCGet`, TLC's random generators, and what the model checker reports through `TLCGet`.
//!
//! The model checker tells the runtime what it is doing: [`Runtime::start`] with its options
//! once it has processed the spec, before it checks the assumptions,
//! [`Runtime::update_statistics`] as it counts states, [`Runtime::set_expanding`] for the state
//! each thread computes successors of, and hooks for the level and the behavior of a state.

use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::AtomicBool;
use std::sync::{Arc, Mutex, RwLock};
use std::thread::{self, ThreadId};
use std::time::{Duration, SystemTime};

use tla_value::{Result, Symbol, Value};

use crate::State;
use crate::stdlib::tlc::{JavaRandom, tlc_fingerprint};

pub struct Runtime {
    /// Lines printed by `Print` and `PrintT`, in order.
    pub output: Mutex<Vec<String>>,
    /// The registers of `TLCSet` and `TLCGet`.
    pub registers: Mutex<Registers>,
    /// Whether `TLCSet("exit", TRUE)` asked the model checker to stop.
    pub is_stopped: AtomicBool,
    checker: RwLock<Checker>,
    random: Mutex<Randomness>,
    started_at: SystemTime,
}

#[derive(Default)]
pub struct Registers {
    /// Set by `TLCSet(i, v)` for a nonnegative integer `i`.
    pub numbered: BTreeMap<i32, Value>,
    /// Set by `TLCSet("s:name", v)`, by the whole key.
    pub named: BTreeMap<Symbol, Value>,
    /// The Java system properties `TLCSet("-Dkey", v)` sets, with the values as TLC prints them.
    pub properties: BTreeMap<String, String>,
    /// The counts of `_Possible!_Track`, by name.
    pub possible: BTreeMap<Symbol, i32>,
}

/// The options of a model-checking run, which `TLCGet("config")` reports. The defaults are
/// those of TLC's command line, as tla-ts gives them.
#[derive(Clone, Debug)]
pub struct CheckerOptions {
    /// The search mode: `"bfs"`, the only one there is yet.
    pub mode: String,
    /// `CHECK_DEADLOCK` of the model configuration, which TLC's `-deadlock` turns off.
    pub check_deadlock: bool,
    /// TLC's `-workers`.
    pub workers: i32,
    /// TLC's `-fp`: the index of the irreducible polynomial fingerprints use.
    pub fingerprint: i32,
    /// The directory TLC is installed in.
    pub install: String,
}

impl Default for CheckerOptions {
    fn default() -> Self {
        Self {
            mode: "bfs".to_owned(),
            check_deadlock: true,
            workers: 1,
            fingerprint: 0,
            install: "unknown".to_owned(),
        }
    }
}

impl CheckerOptions {
    /// The options for a model configuration, with the defaults of TLC's command line.
    pub fn for_config(config: &tla_parser::ModelConfig) -> Self {
        Self { check_deadlock: config.check_deadlock, ..Self::default() }
    }
}

/// The counts TLC reports through `TLCGet`.
#[derive(Clone, Copy, Debug, Default)]
pub struct Statistics {
    pub generated: i64,
    pub distinct: i64,
    pub initial: i64,
    pub queue: i64,
    /// The length of the longest behavior found so far, one for the initial states.
    pub diameter: i64,
}

type Hook<T> = Box<dyn Fn(&State) -> T + Send + Sync>;

#[derive(Default)]
struct Checker {
    /// The counts, once the model checker has started.
    statistics: Option<Statistics>,
    options: CheckerOptions,
    level: Option<Hook<i32>>,
    behavior: Option<Hook<Vec<State>>>,
    spec: Option<Value>,
    counter_example: Option<Value>,
}

/// TLC's `RandomEnumerableValues`: a `java.util.Random` per thread, seeded with `-seed`. The
/// main thread evaluates constants, assumptions, and initial states with the startup generator.
/// A worker reseeds its generator with the fingerprint of each state it expands, XORed with the
/// seed, so a state's successors are the same whatever order the workers expand states in.
struct Randomness {
    seed: i64,
    startup: JavaRandom,
    workers: HashMap<ThreadId, Worker>,
}

#[derive(Default)]
struct Worker {
    /// The state the thread computes the successors of.
    expanding: Option<State>,
    /// How deep the thread is in [`Runtime::at_startup`].
    startup_depth: usize,
    /// The state the generator was last seeded for, and the generator.
    seeded: Option<(State, JavaRandom)>,
}

impl Default for Runtime {
    fn default() -> Self {
        Self {
            output: Mutex::default(),
            registers: Mutex::default(),
            is_stopped: AtomicBool::new(false),
            checker: RwLock::default(),
            random: Mutex::new(Randomness {
                seed: 0,
                startup: JavaRandom::new(0),
                workers: HashMap::new(),
            }),
            started_at: SystemTime::now(),
        }
    }
}

impl Runtime {
    pub fn print(&self, line: String) {
        self.output.lock().unwrap().push(line);
    }

    /// How long ago the runtime was created, which `TLCGet("duration")` reports.
    pub fn elapsed(&self) -> Duration {
        self.started_at.elapsed().unwrap_or_default()
    }

    pub fn started_at(&self) -> SystemTime {
        self.started_at
    }

    /// Records that the model checker has started with `options`, so `TLCGet` can read them
    /// and its counts. TLC creates its model checker once it has processed the spec, before it
    /// checks the assumptions.
    pub fn start(&self, options: CheckerOptions) {
        let mut checker = self.checker.write().unwrap();
        checker.statistics = Some(Statistics { diameter: 1, ..Statistics::default() });
        checker.options = options;
    }

    /// Updates the counts of a started model checker.
    pub fn update_statistics(&self, update: impl FnOnce(&mut Statistics)) {
        if let Some(statistics) = &mut self.checker.write().unwrap().statistics {
            update(statistics);
        }
    }

    /// The counts of the model checker, once it has started.
    pub fn statistics(&self) -> Option<Statistics> {
        self.checker.read().unwrap().statistics
    }

    /// The options of the model checker, TLC's defaults until it starts.
    pub fn options(&self) -> CheckerOptions {
        self.checker.read().unwrap().options.clone()
    }

    /// Sets how `TLCGet("level")` finds the level of a state.
    pub fn on_level(&self, level: impl Fn(&State) -> i32 + Send + Sync + 'static) {
        self.checker.write().unwrap().level = Some(Box::new(level));
    }

    /// Sets how `TLCExt!Trace` finds the behavior that leads to a state.
    pub fn on_behavior(&self, behavior: impl Fn(&State) -> Vec<State> + Send + Sync + 'static) {
        self.checker.write().unwrap().behavior = Some(Box::new(behavior));
    }

    /// Sets what `TLCGet("spec")` reports.
    pub fn set_spec(&self, spec: Value) {
        self.checker.write().unwrap().spec = Some(spec);
    }

    /// Sets the violating behavior `TLCExt!CounterExample` reports.
    pub fn set_counter_example(&self, counter_example: Option<Value>) {
        self.checker.write().unwrap().counter_example = counter_example;
    }

    /// `TLCGet("level")` in `state`, or 0 outside a state.
    pub(crate) fn level(&self, state: Option<&State>) -> i32 {
        let checker = self.checker.read().unwrap();
        match (state, &checker.level) {
            (Some(state), Some(level)) => level(state),
            _ => 0,
        }
    }

    pub(crate) fn behavior(&self, state: &State) -> Option<Vec<State>> {
        self.checker.read().unwrap().behavior.as_ref().map(|behavior| behavior(state))
    }

    pub(crate) fn counter_example(&self) -> Option<Value> {
        self.checker.read().unwrap().counter_example.clone()
    }

    pub(crate) fn spec(&self) -> Option<Value> {
        self.checker.read().unwrap().spec.clone()
    }

    /// Seeds TLC's random generators, as `-seed` does.
    pub fn set_seed(&self, seed: i64) {
        let mut random = self.random.lock().unwrap();
        random.seed = seed;
        random.startup = JavaRandom::new(seed);
        random.workers.values_mut().for_each(|worker| worker.seeded = None);
    }

    pub fn seed(&self) -> i64 {
        self.random.lock().unwrap().seed
    }

    /// Sets the state this thread computes the successors of, whose fingerprint seeds the random
    /// choices made meanwhile, or `None` when it computes none.
    pub fn set_expanding(&self, state: Option<State>) {
        let mut random = self.random.lock().unwrap();
        random.workers.entry(thread::current().id()).or_default().expanding = state;
    }

    /// Runs `evaluate` with the startup generator, as TLC computes constant definitions when it
    /// starts, whichever state the thread is expanding.
    pub fn at_startup<R>(&self, evaluate: impl FnOnce() -> R) -> R {
        struct Startup<'a>(&'a Runtime);
        impl Drop for Startup<'_> {
            fn drop(&mut self) {
                let mut random = self.0.random.lock().unwrap();
                if let Some(worker) = random.workers.get_mut(&thread::current().id()) {
                    worker.startup_depth -= 1;
                }
            }
        }
        self.random
            .lock()
            .unwrap()
            .workers
            .entry(thread::current().id())
            .or_default()
            .startup_depth += 1;
        let _startup = Startup(self);
        evaluate()
    }

    /// Makes random choices with the generator TLC would use on this thread now.
    ///
    /// Choosing can evaluate the spec, which can choose again, so the generator is copied out
    /// while `choose` runs and written back after.
    pub(crate) fn with_random<R>(&self, choose: impl FnOnce(&mut JavaRandom) -> R) -> Result<R> {
        let thread = thread::current().id();
        let (seed, expanding, seeded) = {
            let random = self.random.lock().unwrap();
            let worker = random.workers.get(&thread).filter(|worker| worker.startup_depth == 0);
            let expanding = worker.and_then(|worker| worker.expanding.clone());
            let seeded = match (&expanding, worker.and_then(|worker| worker.seeded.as_ref())) {
                (Some(state), Some((seeded, generator))) if Arc::ptr_eq(state, seeded) => {
                    Some(*generator)
                }
                _ => None,
            };
            (random.seed, expanding, seeded)
        };
        let Some(state) = expanding else {
            let mut generator = self.random.lock().unwrap().startup;
            let result = choose(&mut generator);
            self.random.lock().unwrap().startup = generator;
            return Ok(result);
        };
        let mut generator = match seeded {
            Some(generator) => generator,
            None => JavaRandom::new((tlc_fingerprint(&state)? ^ seed as u64) as i64),
        };
        let result = choose(&mut generator);
        let mut random = self.random.lock().unwrap();
        random.workers.entry(thread).or_default().seeded = Some((state, generator));
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use tla_value::Value;

    use super::{CheckerOptions, Runtime};
    use crate::State;
    use crate::stdlib::tlc::{JavaRandom, tlc_fingerprint};

    fn draw(runtime: &Runtime) -> i32 {
        runtime.with_random(|random| random.next_int(1000)).unwrap()
    }

    #[test]
    fn takes_tlcs_options_from_a_model_configuration() {
        let config =
            tla_parser::parse_config("INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n").unwrap();
        let options = CheckerOptions::for_config(&config);
        assert!(!options.check_deadlock);
        assert_eq!((options.mode.as_str(), options.workers, options.fingerprint), ("bfs", 1, 0));
        assert!(CheckerOptions::for_config(&tla_parser::ModelConfig::default()).check_deadlock);
    }

    #[test]
    fn is_shared_by_worker_threads() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Runtime>();
    }

    #[test]
    fn draws_from_the_startup_generator_outside_a_state() {
        let runtime = Runtime::default();
        runtime.set_seed(7);
        let mut expected = JavaRandom::new(7);
        assert_eq!(draw(&runtime), expected.next_int(1000));
        assert_eq!(draw(&runtime), expected.next_int(1000));
    }

    #[test]
    fn reseeds_for_each_state_a_thread_expands() {
        let runtime = Runtime::default();
        runtime.set_seed(3);
        let state: State = Arc::from(vec![Value::Int(1)]);
        let seed = (tlc_fingerprint(&state).unwrap() ^ 3) as i64;
        runtime.set_expanding(Some(state.clone()));
        let mut expected = JavaRandom::new(seed);
        assert_eq!(draw(&runtime), expected.next_int(1000));
        assert_eq!(draw(&runtime), expected.next_int(1000));
        runtime.set_expanding(Some(Arc::from(vec![Value::Int(1)])));
        assert_eq!(draw(&runtime), JavaRandom::new(seed).next_int(1000));
        let in_startup = runtime.at_startup(|| draw(&runtime));
        assert_eq!(in_startup, JavaRandom::new(3).next_int(1000));
    }

    #[test]
    fn reports_the_model_checker_once_started() {
        let runtime = Runtime::default();
        assert!(runtime.statistics().is_none());
        runtime.update_statistics(|statistics| statistics.distinct = 4);
        assert!(runtime.statistics().is_none());
        let options = CheckerOptions { check_deadlock: false, ..CheckerOptions::default() };
        runtime.start(options);
        runtime.update_statistics(|statistics| statistics.distinct = 4);
        let statistics = runtime.statistics().unwrap();
        assert_eq!((statistics.distinct, statistics.diameter), (4, 1));
        assert!(!runtime.options().check_deadlock);
        runtime.on_level(|state| state.len() as i32);
        assert_eq!(runtime.level(Some(&Arc::from(vec![Value::TRUE; 2]))), 2);
        assert_eq!(runtime.level(None), 0);
    }
}
