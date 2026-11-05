//! Transition systems written by hand, for testing the model checker without successor
//! generation: a module gives the variables and the predicates the model checker evaluates, and
//! a function gives the successors of each state.

use std::sync::Arc;

use tla_tools_eval::{Result, State};
use tla_tools_resolve::{DefId, Spec};
use tla_tools_value::Value;

use crate::{Options, Outcome, Successors, check};

/// The module `M` with `body`, which declares `VARIABLE x`.
pub fn spec(body: &str) -> Spec {
    spec_extending("Naturals, TLC", body)
}

/// The module `M` that extends `modules`, with `body`.
pub fn spec_extending(modules: &str, body: &str) -> Spec {
    let source = format!("---- MODULE M ----\nEXTENDS {modules}\nVARIABLE x\n{body}\n====\n");
    tla_tools_resolve::resolve(&source, &mut |_: &str| None)
        .unwrap_or_else(|error| panic!("{error}"))
}

pub fn state(x: i32) -> State {
    Arc::from(vec![Value::Int(x)])
}

/// The states of `x` from `init`, each with the successors `next` gives it.
pub struct System {
    pub init: Vec<i32>,
    pub next: fn(i32) -> Vec<i32>,
}

impl Successors for System {
    fn init_states(
        &self,
        _init: &[DefId],
        found: &mut dyn FnMut(State) -> Result<bool>,
    ) -> Result<()> {
        for &x in &self.init {
            if !found(state(x))? {
                break;
            }
        }
        Ok(())
    }

    fn next_states(
        &self,
        _next: DefId,
        current: &State,
        found: &mut dyn FnMut(State) -> Result<bool>,
    ) -> Result<()> {
        let Value::Int(x) = current[0] else { panic!("x is an integer") };
        for successor in (self.next)(x) {
            if !found(state(successor))? {
                break;
            }
        }
        Ok(())
    }
}

/// Searches the states of `system` for the module `spec` under the configuration `config`.
pub fn explore(mut spec: Spec, config: &str, system: System) -> crate::search::Search {
    let config = tla_tools_parser::parse_config(config).unwrap_or_else(|error| panic!("{error}"));
    let model =
        tla_tools_eval::bind_model(&spec, &config).unwrap_or_else(|error| panic!("{error:?}"));
    let plan = crate::plan::plan(&mut spec, &config, &Default::default()).unwrap();
    let evaluator = tla_tools_eval::Evaluator::new(Arc::new(spec), model.constants);
    evaluator.runtime().start(tla_tools_eval::CheckerOptions::for_config(&config));
    let order: Vec<usize> = (0..evaluator.spec().variables.len()).collect();
    let fingerprinter =
        crate::fingerprint::Fingerprinter::new(&evaluator, plan.view, config.symmetry, &order)
            .unwrap();
    crate::search::search(
        &system,
        &evaluator,
        &plan,
        &fingerprinter,
        config.check_deadlock,
        &order,
        None,
        &Default::default(),
    )
}

/// Checks the module with `body` under `config` with `workers` workers, exploring `system`.
pub fn run_with_workers(body: &str, config: &str, system: System, workers: usize) -> Outcome {
    let config = tla_tools_parser::parse_config(config).unwrap_or_else(|error| panic!("{error}"));
    check(spec(body), &config, &Options { workers, ..Options::default() }, |_| system)
}

/// Checks the module with `body` under the configuration `config`, exploring `system`.
pub fn run(body: &str, config: &str, system: System) -> Outcome {
    let config = tla_tools_parser::parse_config(config).unwrap_or_else(|error| panic!("{error}"));
    check(spec(body), &config, &Options::default(), |_| system)
}
