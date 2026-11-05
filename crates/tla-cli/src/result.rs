//! What TLC prints once it is done: the verdict, the behavior that leads to a violation, and the
//! counts of the search, as tla-ts's `printResult` prints them.

use std::time::Instant;

use tla_checker::report::{Step, Trace};
use tla_checker::{Outcome, Status};

use crate::printer::{self, Level, Printer};

/// TLC's printed form of a state: `/\ x = 1` for each variable, or `x = 1` for the only one.
pub fn format_state(variables: &[(String, tla_eval::Value)]) -> String {
    let conjunct = if variables.len() == 1 { "" } else { "/\\ " };
    variables
        .iter()
        .map(|(name, value)| {
            format!("{conjunct}{name} = {}\n", tla_eval::pretty_print(&value.to_string()))
        })
        .collect()
}

/// An evaluation error without the line tla-eval adds to say where it happened, which TLC
/// reports in its stack of nested expressions instead.
fn without_location(message: &str) -> &str {
    match message.rsplit_once('\n') {
        Some((text, last))
            if last.starts_with("line ")
                && last.contains(", column ")
                && last.contains(" of module ") =>
        {
            text
        }
        _ => message,
    }
}

/// TLC's headline for a violated temporal property.
fn temporal_headline(names: &[String]) -> String {
    match names {
        [] => "Temporal properties were violated.\n".into(),
        [name] => format!("Temporal property {name} was violated.\n"),
        [rest @ .., last] => {
            let comma = if rest.len() > 1 { "," } else { "" };
            format!("Temporal properties {}{comma} and {last} were violated.\n", rest.join(", "))
        }
    }
}

fn print_trace(printer: &mut Printer, steps: &[Step], heading: &str) {
    if !steps.is_empty() {
        printer.print(Level::Error, heading);
    }
    for (index, step) in steps.iter().enumerate() {
        let action = match (&step.action, index) {
            (Some(action), _) => action.as_str(),
            (None, 0) => "Initial predicate",
            (None, _) => "Unknown action",
        };
        let state = format_state(&step.variables);
        printer.print(Level::State, &format!("{}: <{action}>\n{state}", index + 1));
    }
}

const BEHAVIOR: &str = "The behavior up to this point is:";
const COUNTER_EXAMPLE: &str = "The following behavior constitutes a counter-example:\n";

/// Prints a violation, and returns whether TLC goes on to print the counts of the search.
fn print_violation(printer: &mut Printer, outcome: &Outcome) -> bool {
    let report = &outcome.report;
    if let Some(assumption) = &report.assumption {
        let text = match &assumption.error {
            Some(error) => {
                format!("Evaluating assumption {} failed.\n{error}", assumption.location)
            }
            None => format!("Assumption {} is false.", assumption.location),
        };
        printer.print(Level::Error, &text);
        return false;
    }
    let empty = Trace::default();
    let trace = report.trace.as_ref().unwrap_or(&empty);
    let name = outcome.violation.as_deref().unwrap_or_default();
    let loop_start = trace.loop_start;
    let is_initial = loop_start.is_none()
        && trace.steps.len() == 1
        && matches!(outcome.status, Status::InvariantViolation | Status::LivenessViolation);
    let temporal = || temporal_headline(&report.temporal_properties);
    let headline = match outcome.status {
        Status::Deadlock => "Deadlock reached.".to_owned(),
        Status::InvariantViolation if is_initial => {
            format!("Invariant {name} is violated by the initial state:")
        }
        Status::InvariantViolation => format!("Invariant {name} is violated."),
        Status::PropertyViolation => temporal(),
        Status::LivenessViolation if loop_start.is_some() => temporal(),
        Status::LivenessViolation if is_initial => {
            format!("Property {name} is violated by the initial state:")
        }
        Status::LivenessViolation => format!("Action property {name} is violated."),
        _ => outcome.message.clone().unwrap_or_default(),
    };
    if is_initial {
        let state = format_state(&trace.steps[0].variables);
        printer.print(Level::Error, &format!("{headline}\n{state}"));
        return false;
    }
    printer.print(Level::Error, &headline);
    // A safety property's counterexample ends where it breaks, and a liveness one loops back.
    let is_property = outcome.status == Status::PropertyViolation;
    let is_lasso = loop_start.is_some() && !is_property;
    let heading = if is_property || is_lasso { COUNTER_EXAMPLE } else { BEHAVIOR };
    print_trace(printer, &trace.steps, heading);
    if let (Some(start), true) = (loop_start, is_lasso) {
        if start + 1 == trace.steps.len() {
            printer.print(Level::State, &format!("{}: Stuttering", start + 2));
        } else {
            let action = trace.loop_action.as_ref().map(|action| format!(": <{action}>\n"));
            println!("Back to state {}{}", start + 1, action.unwrap_or_default());
        }
    }
    true
}

/// When TLC started checking the temporal properties, which it reports the end of.
#[derive(Default)]
pub struct Liveness {
    pub started: Option<Instant>,
}

impl Liveness {
    fn print_end(&mut self, printer: &mut Printer) {
        if let Some(started) = self.started.take() {
            let text = format!(
                "Finished checking temporal properties in {} at {}",
                printer::duration(started.elapsed()),
                printer::now()
            );
            printer.print(Level::None, &text);
        }
    }
}

/// Prints what checking found, as TLC does.
pub fn print_outcome(printer: &mut Printer, outcome: &Outcome, liveness: &mut Liveness) {
    let report = &outcome.report;
    match outcome.status {
        Status::Error | Status::Unsupported => {
            let message = without_location(outcome.message.as_deref().unwrap_or_default());
            let text = match outcome.status {
                Status::Unsupported => format!("tla-rs does not support this model yet: {message}"),
                _ => message.to_owned(),
            };
            printer.print(Level::Error, &text);
            if let Some(trace) = &report.trace {
                print_trace(printer, &trace.steps, BEHAVIOR);
            }
            if report.counts.is_none() {
                return;
            }
        }
        Status::Success => {
            liveness.print_end(printer);
            let (distinct, generated) =
                (outcome.distinct.unwrap_or(0), outcome.generated.unwrap_or(0));
            let probability =
                printer::probability(printer::optimistic_probability(distinct, generated));
            let text = format!(
                "Model checking completed. No error has been found.\n  Estimates of the probability that TLC did not check all reachable states\n  because two distinct states had the same fingerprint:\n  calculated (optimistic):  val = {probability}"
            );
            printer.print(Level::None, &text);
        }
        _ => {
            if !print_violation(printer, outcome) {
                return;
            }
        }
    }
    if outcome.status != Status::Success {
        liveness.print_end(printer);
    }
    let counts = report.counts.unwrap_or_default();
    let (generated, distinct, depth) = match outcome.status {
        Status::Success => (
            outcome.generated.unwrap_or(counts.generated),
            outcome.distinct.unwrap_or(counts.distinct),
            outcome.depth.unwrap_or(counts.depth),
        ),
        _ => (counts.generated, counts.distinct, counts.depth),
    };
    let queue = counts.queue;
    let text = format!(
        "{generated} states generated, {distinct} distinct states found, {queue} states left on queue."
    );
    printer.print(Level::None, &text);
    let text = format!("The depth of the complete state graph search is {depth}.");
    printer.print(Level::None, &text);
    if let Some(summary) = report.out_degrees.as_deref().and_then(printer::out_degree) {
        printer.print(Level::None, &summary);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_eval::Value;

    #[test]
    fn formats_a_state_as_tlc_does() {
        let one = vec![("x".to_owned(), Value::Int(1))];
        assert_eq!(format_state(&one), "x = 1\n");
        let two = vec![("x".to_owned(), Value::Int(1)), ("y".to_owned(), Value::Bool(true))];
        assert_eq!(format_state(&two), "/\\ x = 1\n/\\ y = TRUE\n");
    }

    #[test]
    fn leaves_out_the_location_of_an_evaluation_error() {
        let message = "The second argument of \\div is 0.\nline 5, column 28 of module Err";
        assert_eq!(without_location(message), "The second argument of \\div is 0.");
        assert_eq!(without_location("Deadlock reached."), "Deadlock reached.");
    }

    #[test]
    fn names_the_violated_temporal_property() {
        assert_eq!(temporal_headline(&["P".into()]), "Temporal property P was violated.\n");
        let two = ["P".into(), "Q".into()];
        assert_eq!(temporal_headline(&two), "Temporal properties P and Q were violated.\n");
        let three = ["P".into(), "Q".into(), "R".into()];
        let headline = "Temporal properties P, Q, and R were violated.\n";
        assert_eq!(temporal_headline(&three), headline);
        assert_eq!(temporal_headline(&[]), "Temporal properties were violated.\n");
    }
}
