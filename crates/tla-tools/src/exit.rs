//! TLC's exit statuses (`EC.ExitStatus`), as tla-ts's `exit-codes.ts` has them.

use tla_tools_checker::{Outcome, Status};

pub const SUCCESS: i32 = 0;
pub const ASSUMPTION_VIOLATION: i32 = 10;
pub const DEADLOCK: i32 = 11;
pub const SAFETY_VIOLATION: i32 = 12;
pub const LIVENESS_VIOLATION: i32 = 13;
pub const SPEC_EVALUATION_FAILURE: i32 = 75;
pub const SAFETY_EVALUATION_FAILURE: i32 = 76;
pub const SPEC_PARSE_ERROR: i32 = 150;
pub const CONFIG_PARSE_ERROR: i32 = 151;
pub const ERROR: i32 = 255;
/// A command line TLC can't read, for which it prints its usage.
pub const USAGE_ERROR: i32 = 1;

/// The beginnings of the errors TLC reports about the configuration rather than the spec.
const CONFIG_ERRORS: &[&str] = &[
    "The configuration file",
    "TLC found an error in the configuration file",
    "The constant parameter",
    "In the configuration file",
];

/// TLC's exit status for what checking found.
pub fn for_outcome(outcome: &Outcome) -> i32 {
    match outcome.status {
        Status::Success => SUCCESS,
        Status::AssumptionViolation | Status::PostconditionViolation => ASSUMPTION_VIOLATION,
        Status::Deadlock => DEADLOCK,
        Status::InvariantViolation | Status::PropertyViolation => SAFETY_VIOLATION,
        Status::LivenessViolation => LIVENESS_VIOLATION,
        Status::Unsupported => ERROR,
        // TLC exits with its general error status when computing a successor fails.
        Status::Error if outcome.report.trace.is_some() => ERROR,
        Status::Error => for_error(outcome.message.as_deref().unwrap_or_default()),
    }
}

/// TLC's exit status for an error before the search expands a state: one in the
/// configuration, or one evaluating the spec.
fn for_error(message: &str) -> i32 {
    if CONFIG_ERRORS.iter().any(|start| message.starts_with(start)) {
        CONFIG_PARSE_ERROR
    } else if message.starts_with("The invariant") && message.contains("is not a state predicate") {
        SAFETY_EVALUATION_FAILURE
    } else {
        SPEC_EVALUATION_FAILURE
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tells_configuration_errors_from_evaluation_errors() {
        let config = Outcome::error("The constant parameter N is not assigned a value");
        assert_eq!(for_outcome(&config), CONFIG_PARSE_ERROR);
        assert_eq!(for_outcome(&Outcome::error("0^0 is undefined.")), SPEC_EVALUATION_FAILURE);
        assert_eq!(for_outcome(&Outcome::unsupported("RandomElement")), ERROR);
        let invariant = "The invariant Inv is not a state predicate (one with no primes or \
                         temporal operators).";
        assert_eq!(for_outcome(&Outcome::error(invariant)), SAFETY_EVALUATION_FAILURE);
    }
}
