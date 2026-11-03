//! Checks TLA+ models as TLC does with one worker.
//!
//! [`check`] takes a resolved specification and a model configuration. It processes the spec
//! as TLC's `SpecProcessor` does ([`plan`]), checks the assumptions, explores the states breadth
//! first ([`search`]), and reports what TLC would: success with the states generated, the
//! distinct states, and the depth of the search, or the violation and the behavior that leads to
//! it. Liveness isn't checked yet: a model's temporal properties are left out, and its safety
//! part is checked.

mod fingerprint;
mod level;
pub mod plan;
mod postcondition;
pub mod search;
#[cfg(test)]
mod testing;
#[cfg(test)]
mod tests;

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use tla_eval::{CheckerOptions, ConstBinding, Evaluator, bind_model};
use tla_parser::ModelConfig;
use tla_resolve::Spec;

pub use crate::plan::{Check, Plan};
pub use crate::search::{Ending, Successors};

/// A model TLC rejects before it explores any state, with TLC's wording.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub message: String,
}

impl Error {
    pub fn config(message: impl Into<String>) -> Self {
        Self { message: message.into() }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

/// TLC's verdict on a model, as tla-ts's conformance runner compares it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    Success,
    AssumptionViolation,
    InvariantViolation,
    /// A violated property: TLC reports one it checks on the initial states or on each step,
    /// such as `[][A]_v`, as a liveness violation.
    LivenessViolation,
    Deadlock,
    /// A postcondition failed once the search ended, or a `_POSSIBLE` predicate was never
    /// witnessed. TLC exits as for a violated assumption.
    PostconditionViolation,
    Error,
    /// The model uses something the checker doesn't do yet.
    Unsupported,
}

impl Status {
    /// The name tla-ts's records give the status.
    pub fn name(self) -> &'static str {
        match self {
            Status::Success => "success",
            Status::AssumptionViolation => "assumption-violation",
            Status::InvariantViolation => "invariant-violation",
            Status::LivenessViolation => "liveness-violation",
            Status::Deadlock => "deadlock",
            Status::PostconditionViolation => "postcondition-violation",
            Status::Error => "error",
            Status::Unsupported => "unsupported",
        }
    }
}

/// What checking a model found.
#[derive(Clone, Debug)]
pub struct Outcome {
    pub status: Status,
    /// The name of the violated invariant or property.
    pub violation: Option<String>,
    /// The number of states in the behavior that leads to a violation.
    pub trace_length: Option<usize>,
    pub generated: Option<u64>,
    pub distinct: Option<u64>,
    pub depth: Option<u64>,
    /// The error, or what the model uses that isn't supported.
    pub message: Option<String>,
    /// Whether the model has temporal properties the checker left out.
    pub has_liveness: bool,
}

impl Outcome {
    fn new(status: Status) -> Self {
        Self {
            status,
            violation: None,
            trace_length: None,
            generated: None,
            distinct: None,
            depth: None,
            message: None,
            has_liveness: false,
        }
    }

    pub fn error(message: impl Into<String>) -> Self {
        Self { message: Some(message.into()), ..Self::new(Status::Error) }
    }

    pub fn unsupported(message: impl Into<String>) -> Self {
        Self { message: Some(message.into()), ..Self::new(Status::Unsupported) }
    }
}

/// How the model checker runs.
#[derive(Clone, Debug, Default)]
pub struct Options {
    /// TLC's `-seed`, for its random choices.
    pub seed: i64,
    /// Use the CommunityModules' Java overrides, as TLC does with `CommunityModules-deps.jar`.
    pub community_modules: bool,
    /// Let IOUtils run commands.
    pub allow_exec: bool,
}

/// Checks `spec` under `config`, with `successors` computing the states of the evaluator it is
/// given. TLC orders strings by when it reads them, so the caller sets that order
/// ([`tla_eval::value::set_order`]) before it resolves the spec, which builds values.
pub fn check<S: Successors>(
    mut spec: Spec,
    config: &ModelConfig,
    options: &Options,
    successors: impl FnOnce(&Evaluator) -> S,
) -> Outcome {
    let model = match bind_model(&spec, config) {
        Ok(model) => model,
        Err(error) => return Outcome::error(error.message),
    };
    let overrides: HashMap<_, _> = model
        .overrides
        .iter()
        .filter_map(|(def, binding)| match binding {
            ConstBinding::Def(target) => Some((*def, *target)),
            _ => None,
        })
        .collect();
    let mut plan = match plan::plan(&mut spec, config, &overrides) {
        Ok(plan) => plan,
        Err(error) => return Outcome::error(error.message),
    };
    let has_variables = !spec.variables.is_empty();
    let assumptions = spec.assumptions.clone();
    let substitutions: Vec<_> = model
        .constants
        .iter()
        .zip(&spec.constants)
        .filter_map(|(binding, constant)| match binding {
            ConstBinding::Def(def) => Some((constant.name, *def)),
            _ => None,
        })
        .collect();
    let mut evaluator =
        Evaluator::new(Arc::new(spec), model.constants).with_overrides(model.overrides);
    if options.community_modules {
        evaluator = evaluator.with_community_modules();
    }
    let runtime = evaluator.runtime();
    runtime.allow_exec(options.allow_exec);
    runtime.set_seed(options.seed);
    // TLC creates its model checker, whose options TLCGet("config") reads, and computes the
    // constant definitions before it checks the assumptions.
    if let Err(error) = check_substitutions(&evaluator, &substitutions) {
        return Outcome::error(error.message);
    }
    runtime.start(CheckerOptions::for_config(config));
    evaluator.evaluate_constant_definitions();
    if let Err(error) = check_constants(&evaluator, &mut plan) {
        return Outcome::error(error.message);
    }
    let fingerprinter =
        match fingerprint::Fingerprinter::new(&evaluator, plan.view, config.symmetry) {
            Ok(fingerprinter) => fingerprinter,
            Err(error) => return Outcome::error(error.message),
        };
    if let Some(outcome) = check_assumptions(&evaluator, &assumptions) {
        return outcome;
    }
    let has_liveness = !plan.liveness.is_empty() || plan.temporals > 0;
    if !has_variables {
        let outcome = Outcome {
            generated: Some(0),
            distinct: Some(0),
            depth: Some(0),
            ..Outcome::new(Status::Success)
        };
        return Outcome { has_liveness, ..outcome };
    }
    let successors = successors(&evaluator);
    let searched =
        search::search(&successors, &evaluator, &plan, &fingerprinter, config.check_deadlock);
    let mut outcome = match searched.ending {
        Ending::Success => postcondition::check(&evaluator, &plan).unwrap_or(Outcome {
            generated: Some(searched.generated),
            distinct: Some(searched.distinct),
            depth: Some(searched.depth),
            ..Outcome::new(Status::Success)
        }),
        Ending::InvariantViolation(name) => Outcome {
            violation: Some(name),
            trace_length: Some(searched.trace.len()),
            ..Outcome::new(Status::InvariantViolation)
        },
        Ending::PropertyViolation(name) => Outcome {
            violation: Some(name),
            trace_length: Some(searched.trace.len()),
            ..Outcome::new(Status::LivenessViolation)
        },
        Ending::Deadlock => {
            Outcome { trace_length: Some(searched.trace.len()), ..Outcome::new(Status::Deadlock) }
        }
        Ending::Error(message) => Outcome::error(message),
    };
    outcome.has_liveness = has_liveness;
    outcome
}

/// TLC's check of the definitions the configuration substitutes for constants, as in `C <- Foo`,
/// before it creates its model checker: one above constant level must evaluate without a state.
fn check_substitutions(
    evaluator: &Evaluator,
    substitutions: &[(tla_value::Symbol, tla_resolve::DefId)],
) -> Result<(), Error> {
    let levels = level::Levels::sany(level::SUBSTITUTION_STATE_LEVEL_OPERATORS);
    for &(constant, def) in substitutions {
        let spec = evaluator.spec();
        if !spec.def(def).params.is_empty()
            || levels.def_level(spec, def) == tla_resolve::Level::Constant
        {
            continue;
        }
        if evaluator.runtime().at_startup(|| evaluator.eval_def(def, None)).is_err() {
            let target = spec.def(def).name;
            return Err(Error::config(format!(
                "The configuration file substitutes constant {constant} with non-constant {target}"
            )));
        }
    }
    Ok(())
}

/// TLC's checks of the constant-level parts of the spec and the configuration, as it processes
/// the spec: a part that is `TRUE` isn't checked, and others are errors.
fn check_constants(evaluator: &Evaluator, plan: &mut Plan) -> Result<(), Error> {
    for constant in std::mem::take(&mut plan.constants) {
        let value = evaluator.runtime().at_startup(|| evaluator.eval_def(constant.def, None));
        match (&constant.usage, value) {
            (plan::Usage::Conjunct { name, is_spec }, Ok(value)) => {
                let usage = if *is_spec { "spec" } else { "property" };
                match value.as_bool() {
                    Some(true) => {}
                    Some(false) => {
                        return Err(Error::config(format!(
                            "The spec is trivially false because {name} is false."
                        )));
                    }
                    None => {
                        return Err(Error::config(format!(
                            "The operator {name}, which equals {value},\ncannot be used as a {usage}"
                        )));
                    }
                }
            }
            (plan::Usage::Conjunct { .. }, Err(error)) => {
                return Err(Error::config(error.to_string()));
            }
            (plan::Usage::Predicate { kind, name }, Ok(value)) => {
                if value.as_bool() != Some(true) {
                    return Err(Error::config(format!("The {kind} of {name} is equal to {value}")));
                }
                // TLC doesn't check a predicate that is a true constant.
                let lists = [
                    &mut plan.invariants,
                    &mut plan.initial_predicates,
                    &mut plan.constraints,
                    &mut plan.action_constraints,
                ];
                for checks in lists {
                    checks.retain(|check| check.def != constant.def);
                }
            }
            (plan::Usage::Operator { kind, name }, Ok(_)) => {
                return Err(Error::config(format!("The {kind} {name} cannot be a constant.")));
            }
            // TLC keeps a definition that fails to evaluate as an operator.
            (_, Err(_)) => {}
        }
    }
    Ok(())
}

/// The first assumption that fails, as TLC checks them before it explores any state.
fn check_assumptions(evaluator: &Evaluator, assumptions: &[tla_resolve::DefId]) -> Option<Outcome> {
    for &def in assumptions {
        let violation = match evaluator.eval_def(def, None) {
            Ok(value) if value.as_bool() == Some(true) => continue,
            Ok(value) if value.as_bool() == Some(false) => {
                let def = evaluator.spec().def(def);
                let module = evaluator.spec().modules[def.module.index()].name;
                format!("assumption {} of module {module} is false", def.name)
            }
            // TLC reports an assumption it fails to evaluate as violated.
            Ok(value) => format!("assumption evaluated to {value}"),
            Err(error) => error.to_string(),
        };
        return Some(Outcome {
            message: Some(violation),
            trace_length: Some(0),
            ..Outcome::new(Status::AssumptionViolation)
        });
    }
    None
}
