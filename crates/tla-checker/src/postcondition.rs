//! What TLC checks once a search ends without a violation: the `_POSSIBLE` predicates, which
//! some state or step of the model must have witnessed, and the `POSTCONDITION`s, which read the
//! counts of the search through `TLCGet`.

use tla_eval::Evaluator;
use tla_value::Symbol;

use crate::{Outcome, Plan, Status};

/// What TLC finds once a search ends without a violation: a postcondition it computed when it
/// started, which it rejects, a `_POSSIBLE` predicate no state or step witnessed, or the first
/// postcondition that is false or fails.
pub fn check(evaluator: &Evaluator, plan: &Plan) -> Option<Outcome> {
    if let Some(constant) = plan.postconditions.iter().find(|postcondition| {
        postcondition.is_constant
            && postcondition.def.is_some_and(|def| {
                evaluator.runtime().at_startup(|| evaluator.eval_def(def, None)).is_ok()
            })
    }) {
        return Some(Outcome::error(format!(
            "The post condition {} cannot be a constant.",
            constant.name
        )));
    }
    let violation = |name: &str, message: String| Outcome {
        violation: Some(name.to_string()),
        message: Some(message),
        trace_length: Some(0),
        ..Outcome::new(Status::PostconditionViolation)
    };
    let counts = evaluator.runtime().registers.lock().unwrap().possible.clone();
    let possible = plan.possible.iter().chain(&plan.action_possible);
    if let Some(unwitnessed) = possible
        .clone()
        .find(|check| counts.get(&Symbol::intern(&check.name)).is_none_or(|&count| count == 0))
    {
        let name = &unwitnessed.name;
        return Some(violation(
            name,
            format!("The _POSSIBLE predicate {name} was never witnessed."),
        ));
    }
    for postcondition in &plan.postconditions {
        let name = &postcondition.name;
        let value = match postcondition.def {
            Some(def) => evaluator.eval_def(def, None).map_err(|error| error.to_string()),
            None => Err(format!("Unknown operator {name}.")),
        };
        match value {
            Ok(value) if value.as_bool() == Some(true) => {}
            Ok(value) if value.as_bool() == Some(false) => {
                return Some(violation(name, format!("Postcondition {name} is false.")));
            }
            Ok(value) => {
                let message = format!(
                    "Evaluating postcondition {name} failed.\nTLC expected a boolean value, but did not find one. {name} is {value}"
                );
                return Some(violation(name, message));
            }
            Err(error) => {
                let message = format!("Evaluating postcondition {name} failed.\n{error}");
                return Some(violation(name, message));
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use crate::Status;
    use crate::testing::{System, run};

    const SPEC: &str = "Init == x = 0\nNext == x' = x + 1\nSpec == Init /\\ [][Next]_x\n\
        AtTwo == x = 2\nStep == x' = x + 1\nNever == x = 9\n\
        Counted == TLCGet(\"distinct\") = 4\nMiscounted == TLCGet(\"distinct\") = 3\n\
        Constant == TRUE";

    fn counter(x: i32) -> Vec<i32> {
        if x < 3 { vec![x + 1] } else { Vec::new() }
    }

    fn check(config: &str) -> crate::Outcome {
        let config = format!("SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n{config}");
        run(SPEC, &config, System { init: vec![0], next: counter })
    }

    #[test]
    fn needs_a_witness_of_each_possible_predicate() {
        let outcome = check("_POSSIBLE AtTwo Step\nPOSTCONDITION Counted");
        assert_eq!((outcome.status, outcome.generated), (Status::Success, Some(4)));
        let outcome = check("_POSSIBLE AtTwo Never");
        assert_eq!(
            (outcome.status, outcome.violation.as_deref(), outcome.trace_length),
            (Status::PostconditionViolation, Some("Never"), Some(0))
        );
        let outcome = check("_POSSIBLE AtTwo AtTwo");
        assert_eq!(outcome.status, Status::Error);
    }

    #[test]
    fn checks_postconditions_against_the_counts_of_the_search() {
        let outcome = check("POSTCONDITION Miscounted");
        assert_eq!(
            (outcome.status, outcome.message.as_deref()),
            (Status::PostconditionViolation, Some("Postcondition Miscounted is false."))
        );
        // TLC computes a constant definition when it starts, and rejects it as a postcondition.
        let outcome = check("POSTCONDITION Constant");
        assert_eq!(outcome.status, Status::Error);
        // A violation comes first.
        let outcome = run(
            SPEC,
            "SPECIFICATION Spec\nPOSTCONDITION Constant",
            System { init: vec![0], next: counter },
        );
        assert_eq!(outcome.status, Status::Deadlock);
    }
}
