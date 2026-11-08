//! What TLC prints once it is done: the verdict, the behavior that leads to a violation, and the
//! counts of the search, as tla-ts's `printResult` prints them.

use std::time::Instant;

use tla_tools_checker::report::Trace;
use tla_tools_checker::{Outcome, Status};

use tla_tools_checker::message;

use crate::printer::{self, Level, Printer, ec};

/// TLC's printed form of a state: `/\ x = 1` for each variable, or `x = 1` for the only one.
pub fn format_state(variables: &[(String, tla_tools_eval::Value)]) -> String {
    let conjunct = if variables.len() == 1 { "" } else { "/\\ " };
    variables
        .iter()
        .map(|(name, value)| {
            format!("{conjunct}{name} = {}\n", tla_tools_eval::pretty_print(&value.to_string()))
        })
        .collect()
}

/// An evaluation error without the line tla-tools-eval adds to say where it happened, which TLC
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

/// Prints the behavior, with what the spec printed as TLC computed its states again and
/// evaluated their alias: before the heading, before each state, and after the behavior.
fn print_trace(printer: &mut Printer, trace: &Trace, heading: &str) {
    print_lines(&trace.printed_before);
    if !trace.steps.is_empty() {
        let code = match heading {
            BEHAVIOR => ec::TLC_BEHAVIOR_UP_TO_THIS_POINT,
            _ => ec::TLC_COUNTER_EXAMPLE,
        };
        printer.print(code, Level::Error, heading);
    }
    for (index, step) in trace.steps.iter().enumerate() {
        print_lines(&step.printed);
        let action = match (&step.action, index) {
            (Some(action), _) => action.as_str(),
            (None, 0) => "Initial predicate",
            (None, _) => "Unknown action",
        };
        let state = format_state(&step.variables);
        let text = format!("{}: <{action}>\n{state}", index + 1);
        printer.print(ec::TLC_STATE_PRINT2, Level::State, &text);
    }
}

/// Prints what the spec printed, which TLC prints as it is, without a frame under `-tool`.
fn print_lines(lines: &[String]) {
    for line in lines {
        println!("{line}");
    }
}

/// The templates of TLC's messages that report an error with its cause on the lines after.
const WITH_CAUSE: &[(u16, &str, &str)] = &[
    (ec::TLC_INVARIANT_EVALUATION_FAILED, "Evaluating invariant ", " failed."),
    (ec::TLC_ACTION_PROPERTY_EVALUATION_FAILED, "Evaluating action property ", " failed."),
    (ec::TLC_POSTCONDITION_EVALUATION_ERROR, "Evaluating postcondition ", " failed."),
];

/// Prints an error the check ended with, with TLC's code for it. The cause of an error, and an
/// error computing the initial states, are nested as TLC raised them, which under `-tool`
/// frames each with its own code.
fn print_error(printer: &mut Printer, outcome: &Outcome, text: &str) {
    let (first, cause) = text.split_once('\n').unwrap_or((text, ""));
    for &(code, start, end) in WITH_CAUSE {
        if first.starts_with(start) && first.ends_with(end) && !cause.is_empty() {
            let text = format!("{first}\n{}", printer.nested(cause));
            return printer.print(code, Level::Error, &text);
        }
    }
    let report = &outcome.report;
    let initial = report.failure.as_ref().and_then(|failure| failure.initial_state.as_ref());
    if let Some(state) = initial {
        let text = format!(
            "{}\nWhile working on the initial state:\n{}",
            printer.nested(text),
            format_state(state)
        );
        return printer.print(ec::TLC_INITIAL_STATE, Level::Error, &text);
    }
    // TLC reports an error computing the initial states as a general one, with the error it
    // raised, and another error with its own code.
    let is_initial = report.counts.is_some() && report.trace.is_none();
    if is_initial && outcome.status == Status::Error {
        return printer.print(ec::GENERAL, Level::Error, &printer.nested(text));
    }
    let code = match outcome.status {
        Status::Error => message::code_of(text).unwrap_or(ec::GENERAL),
        _ => ec::GENERAL,
    };
    printer.print(code, Level::Error, text);
}

/// TLC's message with the call stack of an error, from the outermost expression in.
fn nested_expressions(call_stack: &[String]) -> String {
    let positions = match call_stack {
        [] => "    The error call stack is empty.\n".to_owned(),
        _ => {
            let lines = call_stack.iter().enumerate();
            let lines: String = lines.map(|(index, line)| format!("{index}. {line}\n")).collect();
            format!("{lines}\n")
        }
    };
    format!(
        "The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n{positions}"
    )
}

const BEHAVIOR: &str = "The behavior up to this point is:";
const COUNTER_EXAMPLE: &str = "The following behavior constitutes a counter-example:\n";

/// Prints a violation, and returns whether TLC goes on to print the counts of the search.
fn print_violation(printer: &mut Printer, outcome: &Outcome) -> bool {
    let report = &outcome.report;
    if let Some(assumption) = &report.assumption {
        let (code, text) = match &assumption.error {
            Some(error) => {
                let text = format!(
                    "Evaluating assumption {} failed.\n{}",
                    assumption.location,
                    printer.nested(error)
                );
                (ec::TLC_ASSUMPTION_EVALUATION_ERROR, text)
            }
            None => {
                (ec::TLC_ASSUMPTION_FALSE, format!("Assumption {} is false.", assumption.location))
            }
        };
        printer.print(code, Level::Error, &text);
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
    let (code, headline) = match outcome.status {
        Status::Deadlock => (ec::TLC_DEADLOCK_REACHED, "Deadlock reached.".to_owned()),
        Status::InvariantViolation if is_initial => (
            ec::TLC_INVARIANT_VIOLATED_INITIAL,
            format!("Invariant {name} is violated by the initial state:"),
        ),
        Status::InvariantViolation => {
            (ec::TLC_INVARIANT_VIOLATED_BEHAVIOR, format!("Invariant {name} is violated."))
        }
        Status::PropertyViolation => (ec::TLC_TEMPORAL_PROPERTY_VIOLATED, temporal()),
        Status::LivenessViolation if loop_start.is_some() => {
            (ec::TLC_TEMPORAL_PROPERTY_VIOLATED, temporal())
        }
        Status::LivenessViolation if is_initial => (
            ec::TLC_PROPERTY_VIOLATED_INITIAL,
            format!("Property {name} is violated by the initial state:"),
        ),
        Status::LivenessViolation => (
            ec::TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR,
            format!("Action property {name} is violated."),
        ),
        _ => (ec::GENERAL, outcome.message.clone().unwrap_or_default()),
    };
    print_lines(&trace.printed_first);
    if is_initial {
        let state = format_state(&trace.steps[0].variables);
        printer.print(code, Level::Error, &format!("{headline}\n{state}"));
        return false;
    }
    printer.print(code, Level::Error, &headline);
    // A safety property's counterexample ends where it breaks, and a liveness one loops back.
    let is_property = outcome.status == Status::PropertyViolation;
    let is_lasso = loop_start.is_some() && !is_property;
    let heading = if is_property || is_lasso { COUNTER_EXAMPLE } else { BEHAVIOR };
    print_trace(printer, trace, heading);
    if let (Some(start), true) = (loop_start, is_lasso) {
        if start + 1 == trace.steps.len() {
            let text = format!("{}: Stuttering", start + 2);
            printer.print(ec::TLC_STATE_PRINT3, Level::State, &text);
        } else {
            print_lines(&trace.loop_printed);
            print_back_to_state(printer, start + 1, trace.loop_action.as_deref());
        }
    }
    print_lines(&trace.printed_last);
    true
}

/// Prints the state a behavior loops back to. TLC prints it as a message, or under `-tool` as
/// a state, which TLC formats as it formats the other states for the Toolbox.
fn print_back_to_state(printer: &mut Printer, number: usize, action: Option<&str>) {
    if printer.is_tool() {
        let text = match action {
            Some(action) => format!("{number}: Back to state: <{action}>\n"),
            None => format!("{number}: Back to state\n"),
        };
        return printer.print(ec::TLC_BACK_TO_STATE, Level::State, &text);
    }
    let action = action.map(|action| format!(": <{action}>\n"));
    println!("Back to state {number}{}", action.unwrap_or_default());
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
            printer.print(ec::TLC_CHECKING_TEMPORAL_PROPS_END, Level::None, &text);
        }
    }
}

/// Prints the counts of the search again as progress, which TLC does under `-tool` so that the
/// Toolbox shows them as it shows all progress, with the states per minute since TLC started.
fn print_final_progress(printer: &mut Printer, counts: (u64, u64, u64, u64), started: Instant) {
    let (generated, distinct, queue, depth) = counts;
    let minutes = started.elapsed().as_millis() as f64 / 60_000.0;
    // Java's cast of the rate, which saturates as Rust's does.
    let per_minute = |count: u64| printer::grouped((count as f64 / minutes) as i64 as u64);
    let text = format!(
        "Progress({}) at {}: {} states generated ({} s/min), {} distinct states found ({} ds/min), {} states left on queue.",
        depth.max(1),
        printer::now(),
        printer::grouped(generated),
        per_minute(generated),
        printer::grouped(distinct),
        per_minute(distinct),
        printer::grouped(queue),
    );
    printer.print(ec::TLC_PROGRESS_STATS, Level::None, &text);
}

/// Prints what checking found, as TLC does, for a check that started at `started`.
pub fn print_outcome(
    printer: &mut Printer,
    outcome: &Outcome,
    liveness: &mut Liveness,
    started: Instant,
) {
    let report = &outcome.report;
    match outcome.status {
        Status::Error | Status::Unsupported => {
            let message = without_location(outcome.message.as_deref().unwrap_or_default());
            let text = match outcome.status {
                Status::Unsupported => format!("tla-rs does not support this model yet: {message}"),
                _ => message.to_owned(),
            };
            // TLC prints the initial state a check failed on with the error.
            print_error(printer, outcome, &text);
            if let Some(trace) = &report.trace {
                print_trace(printer, trace, BEHAVIOR);
                print_lines(&trace.printed_last);
            }
            if let Some(failure) = &report.failure {
                print_lines(&failure.printed);
                if let Some(call_stack) = &failure.call_stack {
                    let text = nested_expressions(call_stack);
                    printer.print(ec::TLC_NESTED_EXPRESSION, Level::Error, &text);
                }
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
            printer.print(ec::TLC_SUCCESS, Level::None, &text);
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
    if printer.is_tool() {
        print_final_progress(printer, (generated, distinct, queue, depth), started);
    }
    let text = format!(
        "{generated} states generated, {distinct} distinct states found, {queue} states left on queue."
    );
    printer.print(ec::TLC_STATS, Level::None, &text);
    let text = format!("The depth of the complete state graph search is {depth}.");
    printer.print(ec::TLC_SEARCH_DEPTH, Level::None, &text);
    if let Some(summary) = report.out_degrees.as_deref().and_then(printer::out_degree) {
        printer.print(ec::TLC_STATE_GRAPH_OUTDEGREE, Level::None, &summary);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tla_tools_eval::Value;

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
