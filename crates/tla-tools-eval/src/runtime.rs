//! What TLC's operators with effects use: printed output, the registers of `TLCSet` and
//! `TLCGet`, TLC's random generators, and what the model checker reports through `TLCGet`.
//!
//! The model checker tells the runtime what it is doing: [`Runtime::start`] with its options
//! once it has processed the spec, before it checks the assumptions,
//! [`Runtime::update_statistics`] as it counts states, [`Runtime::set_expanding`] for the state
//! each thread computes successors of, and hooks for the level and the behavior of a state.

use std::collections::{BTreeMap, HashMap};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, OnceLock, RwLock};
use std::thread::{self, ThreadId};
use std::time::{Duration, SystemTime};

use tla_tools_value::{Result, Symbol, Value};

use crate::State;
use crate::stdlib::tlc::{JavaRandom, tlc_fingerprint};

pub struct Runtime {
    /// Lines printed by `Print` and `PrintT`, in order, unless [`Runtime::set_printer`] gave
    /// them somewhere to go.
    pub output: Mutex<Vec<String>>,
    /// Where lines printed by `Print` and `PrintT` go as they are printed.
    printer: RwLock<Option<Printer>>,
    /// The lines printed while [`Runtime::capture`] runs, which go nowhere else.
    captured: Mutex<Option<Vec<String>>>,
    /// The registers of `TLCSet` and `TLCGet`.
    pub registers: Mutex<Registers>,
    /// Whether `TLCSet("exit", TRUE)` asked the model checker to stop.
    pub is_stopped: AtomicBool,
    /// Whether an error records the expressions it passes through, as TLC's CallStackTool does.
    records_call_stack: AtomicBool,
    /// Whether IOUtils' `IOExec` and its kin may run commands.
    allows_exec: AtomicBool,
    /// Whether TLC reports warnings, which its `-nowarning` turns off.
    warnings: AtomicBool,
    /// The environment variables IOUtils' `IOEnv` reports, as a record.
    environment: OnceLock<Value>,
    checker: RwLock<Checker>,
    random: Mutex<Randomness>,
    started_at: SystemTime,
    /// The values `TLCCache` keeps.
    cache: Mutex<Cache>,
}

/// The values `TLCCache` keeps, by the address of the expression and then by the closure: those
/// of expressions that don't read the state, and those of the others for the last state read.
#[derive(Default)]
struct Cache {
    constant: CachedValues,
    state: Option<(State, CachedValues)>,
}

/// The values of each expression, by its address, with the closures they were computed with.
type CachedValues = HashMap<usize, Vec<(Value, Value)>>;

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
    pub fn for_config(config: &tla_tools_parser::ModelConfig) -> Self {
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

/// Takes each line `Print` and `PrintT` print.
pub type Printer = Box<dyn Fn(String) + Send + Sync>;

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
    /// The variables in TLC's order, by their index in the state, which TLC's fingerprint of a
    /// state follows, if not the order they are declared in.
    variable_order: Option<Vec<usize>>,
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
            printer: RwLock::default(),
            captured: Mutex::default(),
            registers: Mutex::default(),
            is_stopped: AtomicBool::new(false),
            records_call_stack: AtomicBool::new(false),
            allows_exec: AtomicBool::new(false),
            warnings: AtomicBool::new(true),
            environment: OnceLock::new(),
            checker: RwLock::default(),
            random: Mutex::new(Randomness {
                seed: 0,
                startup: JavaRandom::new(0),
                workers: HashMap::new(),
                variable_order: None,
            }),
            started_at: SystemTime::now(),
            cache: Mutex::default(),
        }
    }
}

impl Runtime {
    /// The value `TLCCache` keeps for the expression at `key` with `closure`, in `state` if the
    /// expression reads it.
    pub(crate) fn cached(
        &self,
        key: usize,
        state: Option<&State>,
        closure: &Value,
    ) -> Result<Option<Value>> {
        let cache = self.cache.lock().unwrap();
        let values = match (state, &cache.state) {
            (None, _) => cache.constant.get(&key),
            (Some(state), Some((cached, values))) if Arc::ptr_eq(state, cached) => values.get(&key),
            (Some(_), _) => None,
        };
        for (cached, value) in values.into_iter().flatten() {
            if cached.equals(closure)? {
                return Ok(Some(value.clone()));
            }
        }
        Ok(None)
    }

    /// Keeps the value of the expression at `key` with `closure` for `TLCCache`.
    pub(crate) fn cache(&self, key: usize, state: Option<State>, closure: Value, value: Value) {
        let mut cache = self.cache.lock().unwrap();
        let values = match state {
            None => &mut cache.constant,
            Some(state) => {
                let is_same =
                    matches!(&cache.state, Some((cached, _)) if Arc::ptr_eq(&state, cached));
                if !is_same {
                    cache.state = Some((state, HashMap::new()));
                }
                &mut cache.state.as_mut().expect("the state was just set").1
            }
        };
        values.entry(key).or_default().push((closure, value));
    }

    /// Prints a line of `Print` or `PrintT`: hands it to the printer, or keeps it in
    /// [`Runtime::output`] without one.
    pub fn print(&self, line: String) {
        if let Some(captured) = &mut *self.captured.lock().unwrap() {
            captured.push(line);
            return;
        }
        match &*self.printer.read().unwrap() {
            Some(printer) => printer(line),
            None => self.output.lock().unwrap().push(line),
        }
    }

    /// Sends the lines `Print` and `PrintT` print to `printer` as they are printed, as TLC
    /// prints them to standard output, instead of keeping them in [`Runtime::output`].
    pub fn set_printer(&self, printer: impl Fn(String) + Send + Sync + 'static) {
        *self.printer.write().unwrap() = Some(Box::new(printer));
    }

    /// Runs `run` and returns the lines `Print` and `PrintT` print meanwhile, instead of
    /// printing them, as the model checker does to print them where TLC does.
    pub fn capture<T>(&self, run: impl FnOnce() -> T) -> (T, Vec<String>) {
        let outer = self.captured.lock().unwrap().replace(Vec::new());
        let result = run();
        let mut captured = self.captured.lock().unwrap();
        let lines = std::mem::replace(&mut *captured, outer).unwrap_or_default();
        (result, lines)
    }

    /// Runs `run` with each error recording the expressions it passes through in its
    /// [`EvalError::call_stack`](crate::EvalError::call_stack), as TLC's CallStackTool does when
    /// TLC computes the initial states or the successors of a state again to find where an
    /// error occurred.
    pub fn record_call_stack<T>(&self, run: impl FnOnce() -> T) -> T {
        let outer = self.records_call_stack.swap(true, Ordering::SeqCst);
        let result = run();
        self.records_call_stack.store(outer, Ordering::SeqCst);
        result
    }

    pub(crate) fn records_call_stack(&self) -> bool {
        self.records_call_stack.load(Ordering::Relaxed)
    }

    /// Lets IOUtils' `IOExec`, `IOEnvExec`, `IOExecTemplate`, and `IOEnvExecTemplate` run the
    /// commands a spec gives them, which they refuse to do by default.
    pub fn allow_exec(&self, allows_exec: bool) {
        self.allows_exec.store(allows_exec, Ordering::SeqCst);
    }

    pub fn allows_exec(&self) -> bool {
        self.allows_exec.load(Ordering::SeqCst)
    }

    /// Turns TLC's warnings on or off, as its `-nowarning` does. Besides the warnings, it
    /// decides whether `getNextStates` stops walking an action once every variable has a value,
    /// which TLC does only with warnings on, and so how many states a disjunction generates.
    pub fn set_warnings(&self, warnings: bool) {
        self.warnings.store(warnings, Ordering::SeqCst);
    }

    pub fn warnings(&self) -> bool {
        self.warnings.load(Ordering::Relaxed)
    }

    /// Sets the environment variables `IOEnv` reports in place of the process's. It has no
    /// effect once `IOEnv` has read them, since TLC reads them once.
    pub fn set_environment(&self, variables: impl IntoIterator<Item = (String, String)>) {
        let _ = self.environment.set(environment_record(variables));
    }

    /// The environment variables, as IOUtils' `IOEnv` reports them: a record from each name to
    /// its value, read once.
    pub(crate) fn environment(&self) -> Value {
        let variables = std::env::vars_os().map(|(name, value)| {
            (name.to_string_lossy().into_owned(), value.to_string_lossy().into_owned())
        });
        self.environment.get_or_init(|| environment_record(variables)).clone()
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

    /// `TLCGet("level")` in a state still being assigned, which is none the model checker has
    /// found: as in tla-ts, the level after the state being expanded, or 0 for an initial state.
    pub(crate) fn assigned_level(&self) -> i32 {
        let assigned: State = Arc::from([]);
        self.level(Some(&assigned))
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

    /// Gives TLC's order of the variables, by their index in the state, which the fingerprint of
    /// a state that seeds a random generator follows.
    pub fn set_variable_order(&self, order: Vec<usize>) {
        let is_declared = order.iter().enumerate().all(|(position, &index)| position == index);
        self.random.lock().unwrap().variable_order = (!is_declared).then_some(order);
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
            None => {
                let order = self.random.lock().unwrap().variable_order.clone();
                let fingerprint = match order {
                    Some(order) => {
                        let values: Vec<Value> =
                            order.iter().map(|&index| state[index].clone()).collect();
                        tlc_fingerprint(&values)?
                    }
                    None => tlc_fingerprint(&state)?,
                };
                JavaRandom::new((fingerprint ^ seed as u64) as i64)
            }
        };
        let result = choose(&mut generator);
        let mut random = self.random.lock().unwrap();
        random.workers.entry(thread).or_default().seeded = Some((state, generator));
        Ok(result)
    }
}

fn environment_record(variables: impl IntoIterator<Item = (String, String)>) -> Value {
    let fields =
        variables.into_iter().map(|(name, value)| (Symbol::intern(&name), Value::str(&value)));
    Value::record(fields.collect())
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use tla_tools_value::Value;

    use super::{CheckerOptions, Runtime};
    use crate::State;
    use crate::stdlib::tlc::{JavaRandom, tlc_fingerprint};

    fn draw(runtime: &Runtime) -> i32 {
        runtime.with_random(|random| random.next_int(1000)).unwrap()
    }

    #[test]
    fn takes_tlcs_options_from_a_model_configuration() {
        let config =
            tla_tools_parser::parse_config("INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n").unwrap();
        let options = CheckerOptions::for_config(&config);
        assert!(!options.check_deadlock);
        assert_eq!((options.mode.as_str(), options.workers, options.fingerprint), ("bfs", 1, 0));
        assert!(
            CheckerOptions::for_config(&tla_tools_parser::ModelConfig::default()).check_deadlock
        );
    }

    #[test]
    fn prints_to_the_printer_or_keeps_the_lines() {
        let runtime = Runtime::default();
        runtime.print("kept".into());
        assert_eq!(*runtime.output.lock().unwrap(), ["kept"]);
        let printed = Arc::new(std::sync::Mutex::new(Vec::new()));
        let sink = printed.clone();
        runtime.set_printer(move |line| sink.lock().unwrap().push(line));
        runtime.print("printed".into());
        let ((), captured) = runtime.capture(|| {
            runtime.print("outer".into());
            let ((), inner) = runtime.capture(|| runtime.print("inner".into()));
            assert_eq!(inner, ["inner"]);
        });
        assert_eq!(captured, ["outer"]);
        runtime.print("after".into());
        assert_eq!(*printed.lock().unwrap(), ["printed", "after"]);
        assert_eq!(*runtime.output.lock().unwrap(), ["kept"]);
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

    /// TLC fingerprints the state that seeds a generator with its variables in TLC's order.
    #[test]
    fn seeds_with_the_state_in_tlcs_variable_order() {
        let runtime = Runtime::default();
        runtime.set_seed(3);
        runtime.set_variable_order(vec![1, 0]);
        let reversed = [Value::Int(2), Value::Int(1)];
        let seed = (tlc_fingerprint(&reversed).unwrap() ^ 3) as i64;
        runtime.set_expanding(Some(Arc::from(vec![Value::Int(1), Value::Int(2)])));
        assert_eq!(draw(&runtime), JavaRandom::new(seed).next_int(1000));
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
