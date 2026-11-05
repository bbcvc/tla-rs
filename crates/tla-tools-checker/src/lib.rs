//! Checks TLA+ models as TLC does with one worker.
//!
//! [`check`] takes a resolved specification and a model configuration. It processes the spec
//! as TLC's `SpecProcessor` does ([`plan`]), checks the assumptions, explores the states breadth
//! first ([`search`]), and reports what TLC would: success with the states generated, the
//! distinct states, and the depth of the search, or the violation and the behavior that leads to
//! it. It checks the temporal properties as TLC does with `-lncheck final`, once the search is
//! done.

mod fingerprint;
mod level;
mod liveness;
pub mod load;
pub mod plan;
mod postcondition;
pub mod progress;
mod purity;
pub mod report;
pub mod search;
#[cfg(test)]
mod testing;
#[cfg(test)]
mod tests;

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use tla_tools_eval::{CheckerOptions, ConstBinding, Evaluator, JavaOverrideError, bind_model};
use tla_tools_parser::ModelConfig;
use tla_tools_resolve::{ModuleId, Spec};

pub use crate::plan::{Check, Plan};
pub use crate::progress::{Counts, Event, Progress};
pub use crate::report::Report;
pub use crate::search::{Ending, Successors};

/// A model TLC rejects before it explores any state, with TLC's wording, or one that uses what
/// the checker doesn't support.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub message: String,
    pub is_unsupported: bool,
}

impl Error {
    pub fn config(message: impl Into<String>) -> Self {
        Self { message: message.into(), is_unsupported: false }
    }

    pub fn unsupported(message: impl Into<String>) -> Self {
        Self { message: message.into(), is_unsupported: true }
    }
}

impl From<Error> for Outcome {
    fn from(error: Error) -> Self {
        match error.is_unsupported {
            true => Outcome::unsupported(error.message),
            false => Outcome::error(error.message),
        }
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
    /// A temporal property TLC finds violated as it builds the behavior graph.
    PropertyViolation,
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
            Status::PropertyViolation => "property-violation",
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
    /// What TLC prints about the check beyond the verdict.
    pub report: Report,
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
            report: Report::default(),
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
    /// The Java class files beside the spec, by the name of the module whose operators TLC
    /// overrides with their public static methods.
    pub classes: HashMap<String, Vec<u8>>,
    /// TLC's order of the variables ([`tla_tools_resolve::tlc_variable_order`]), which TLC's
    /// fingerprint of a state follows. Without it, the order they are declared in.
    pub variable_order: Option<Vec<String>>,
    /// TLC's `-nowarning`, which also changes how many states a disjunction in an action
    /// generates once every variable has a value. TLC records its expected results with it.
    pub nowarning: bool,
    /// TLC's `-workers`: how many threads expand states. With more than one, the search
    /// expands each level of the state graph in parallel where the order can't show (see
    /// [`search::parallel`]); with one, or where it can, it runs as TLC's `-workers 1` does.
    pub workers: usize,
    /// Where the checker reports what it does as it runs.
    pub progress: Progress,
}

/// Checks `spec` under `config`, with `successors` computing the states of the evaluator it is
/// given. TLC orders strings by when it reads them, so the caller sets that order
/// ([`tla_tools_eval::value::set_order`]) before it resolves the spec, which builds values.
pub fn check<S: Successors + Sync>(
    mut spec: Spec,
    config: &ModelConfig,
    options: &Options,
    successors: impl FnOnce(&Evaluator) -> S,
) -> Outcome {
    let mut model = match bind_model(&spec, config) {
        Ok(model) => model,
        Err(error) => return Outcome::error(error.message),
    };
    // The configuration overrides a definition a Java class overrides.
    for (index, module) in spec.modules.iter().enumerate() {
        let Some(class) = options.classes.get(module.name.as_str()) else { continue };
        match tla_tools_eval::java_overrides(&spec, ModuleId(index as u32), class) {
            Ok(overrides) => drop(model.overrides.splice(0..0, overrides)),
            Err(JavaOverrideError::Unsupported(message)) => return Outcome::unsupported(message),
            Err(JavaOverrideError::Invalid(message)) => return Outcome::error(message),
        }
    }
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
        Err(error) => return error.into(),
    };
    let has_variables = !spec.variables.is_empty();
    let tlc_order = tlc_order(&spec, options.variable_order.as_deref());
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
    runtime.set_warnings(!options.nowarning);
    runtime.set_seed(options.seed);
    runtime.set_variable_order(tlc_order.clone());
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
        match fingerprint::Fingerprinter::new(&evaluator, plan.view, config.symmetry, &tlc_order) {
            Ok(fingerprinter) => fingerprinter,
            Err(error) => return Outcome::error(error.message),
        };
    // TLC builds the liveness checker, which translates the temporal formulas, before it
    // checks the assumptions, and only for a spec with variables.
    let liveness = match has_variables {
        true => match liveness::checker::Checker::new(
            &evaluator,
            &plan,
            &overrides,
            plan.view.is_some() || config.symmetry.is_some(),
        ) {
            Ok(liveness) => liveness,
            Err(message) => return Outcome::error(message),
        },
        false => None,
    };
    if let Some(liveness) = &liveness {
        options.progress.report(Event::TemporalBranches(liveness.branches()));
    }
    if let Some(outcome) = check_assumptions(&evaluator, &assumptions) {
        return outcome;
    }
    if !has_variables {
        return Outcome {
            generated: Some(0),
            distinct: Some(0),
            depth: Some(0),
            ..Outcome::new(Status::Success)
        };
    }
    let successors = successors(&evaluator);
    // Several workers find the same states as one only for a model they search without
    // liveness, postconditions, or effects; and only one worker reports a violation as TLC's
    // first one, so they leave that to it.
    let is_parallel = options.workers > 1
        && liveness.is_none()
        && plan.postconditions.is_empty()
        && plan.possible.is_empty()
        && plan.action_possible.is_empty()
        && options.classes.is_empty()
        && purity::is_pure(evaluator.spec(), &plan, &overrides);
    let parallel = match is_parallel {
        true => search::parallel::search(
            &successors,
            &evaluator,
            &plan,
            &fingerprinter,
            config.check_deadlock,
            options.workers,
            &options.progress,
        ),
        false => Err(false),
    };
    let searched = match parallel {
        Ok(searched) => searched,
        Err(computed) => {
            // What the workers reported isn't reported again.
            let progress = match is_parallel {
                true => options.progress.after_initial_states(computed),
                false => options.progress.clone(),
            };
            search::search(
                &successors,
                &evaluator,
                &plan,
                &fingerprinter,
                config.check_deadlock,
                &tlc_order,
                liveness,
                &progress,
            )
        }
    };
    let report = report(&evaluator, &tlc_order, &searched);
    let outcome = match searched.ending {
        Ending::Success => postcondition::check(&evaluator, &plan).unwrap_or(Outcome {
            generated: Some(searched.generated),
            distinct: Some(searched.distinct),
            depth: Some(searched.depth),
            ..Outcome::new(Status::Success)
        }),
        Ending::InvariantViolation(name) => Outcome {
            violation: Some(name),
            trace_length: Some(searched.trace_length),
            ..Outcome::new(Status::InvariantViolation)
        },
        Ending::PropertyViolation(name) => Outcome {
            violation: Some(name),
            trace_length: Some(searched.trace_length),
            ..Outcome::new(Status::LivenessViolation)
        },
        Ending::Deadlock => {
            Outcome { trace_length: Some(searched.trace_length), ..Outcome::new(Status::Deadlock) }
        }
        Ending::LivenessViolation => Outcome {
            trace_length: Some(searched.trace_length),
            ..Outcome::new(Status::LivenessViolation)
        },
        Ending::TemporalViolation => Outcome {
            trace_length: Some(searched.trace_length),
            ..Outcome::new(Status::PropertyViolation)
        },
        Ending::Error(message) => Outcome::error(message),
    };
    Outcome { report, ..outcome }
}

/// What TLC prints about the search beyond its verdict.
fn report(evaluator: &Evaluator, tlc_order: &[usize], searched: &search::Search) -> Report {
    let spec = evaluator.spec();
    let steps = searched
        .trace
        .iter()
        .zip(&searched.actions)
        .map(|(state, action)| report::Step {
            action: action.clone(),
            variables: tlc_order
                .iter()
                .map(|&index| (spec.variables[index].name.to_string(), state[index].clone()))
                .collect(),
        })
        .collect();
    let trace = (!searched.trace.is_empty()).then(|| report::Trace {
        steps,
        loop_start: searched.loop_start,
        loop_action: searched.loop_action.clone(),
    });
    let is_complete = searched.ending == Ending::Success;
    Report {
        trace,
        counts: Some(searched.counts),
        out_degrees: is_complete.then(|| searched.out_degrees.clone()),
        assumption: None,
        temporal_properties: searched.violated.clone(),
    }
}

/// TLC's check of the definitions the configuration substitutes for constants, as in `C <- Foo`,
/// before it creates its model checker: one above constant level must evaluate without a state.
fn check_substitutions(
    evaluator: &Evaluator,
    substitutions: &[(tla_tools_value::Symbol, tla_tools_resolve::DefId)],
) -> Result<(), Error> {
    let levels = level::Levels::sany(level::SUBSTITUTION_STATE_LEVEL_OPERATORS);
    for &(constant, def) in substitutions {
        let spec = evaluator.spec();
        if !spec.def(def).params.is_empty()
            || levels.def_level(spec, def) == tla_tools_resolve::Level::Constant
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

/// The index of each variable of `spec` in TLC's `order` of the variables, those it doesn't
/// name last.
fn tlc_order(spec: &Spec, order: Option<&[String]>) -> Vec<usize> {
    let mut indices: Vec<usize> = (0..spec.variables.len()).collect();
    if let Some(order) = order {
        let position = |index: &usize| {
            let name = spec.variables[*index].name.as_str();
            order.iter().position(|known| known == name).unwrap_or(order.len())
        };
        indices.sort_by_key(position);
    }
    indices
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
fn check_assumptions(
    evaluator: &Evaluator,
    assumptions: &[tla_tools_resolve::DefId],
) -> Option<Outcome> {
    for &def in assumptions {
        let (violation, error) = match evaluator.eval_def(def, None) {
            Ok(value) if value.as_bool() == Some(true) => continue,
            Ok(value) if value.as_bool() == Some(false) => {
                let def = evaluator.spec().def(def);
                let module = evaluator.spec().modules[def.module.index()].name;
                (format!("assumption {} of module {module} is false", def.name), None)
            }
            // TLC reports an assumption it fails to evaluate as violated.
            Ok(value) => {
                let message = format!("assumption evaluated to {value}");
                (message.clone(), Some(message))
            }
            Err(error) => (error.to_string(), Some(error.to_string())),
        };
        let spec = evaluator.spec();
        let location = match &spec.def(def).body {
            tla_tools_resolve::DefBody::Expr(expr) => {
                plan::describe_range(spec, spec.def(def).module, expr.span)
            }
            _ => spec.def(def).name.to_string(),
        };
        let report = Report {
            assumption: Some(report::Assumption { location, error }),
            ..Report::default()
        };
        return Some(Outcome {
            message: Some(violation),
            trace_length: Some(0),
            report,
            ..Outcome::new(Status::AssumptionViolation)
        });
    }
    None
}
