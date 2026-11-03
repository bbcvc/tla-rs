use crate::Status;
use crate::testing::{System, run};

const SPEC: &str = "Init == x = 0\nNext == x' = x + 1\nSpec == Init /\\ [][Next]_x";

fn counter(x: i32) -> Vec<i32> {
    if x < 3 { vec![x + 1] } else { Vec::new() }
}

/// 0 goes to 1 and 2, both go to 3, and 3 to itself.
fn diamond(x: i32) -> Vec<i32> {
    match x {
        0 => vec![1, 2],
        1 | 2 => vec![3],
        _ => vec![3],
    }
}

fn counts(outcome: &crate::Outcome) -> (Status, Option<u64>, Option<u64>, Option<u64>) {
    (outcome.status, outcome.generated, outcome.distinct, outcome.depth)
}

#[test]
fn counts_states_as_tlc_does() {
    let config = "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE";
    let outcome = run(SPEC, config, System { init: vec![0], next: counter });
    assert_eq!(counts(&outcome), (Status::Success, Some(4), Some(4), Some(4)));
    // Repeats count as generated, and the initial states too.
    let outcome = run(SPEC, config, System { init: vec![0, 0], next: diamond });
    assert_eq!(counts(&outcome), (Status::Success, Some(7), Some(4), Some(3)));
}

#[test]
fn reports_a_deadlock_with_the_behavior_to_it() {
    let outcome = run(SPEC, "SPECIFICATION Spec", System { init: vec![0], next: counter });
    assert_eq!((outcome.status, outcome.trace_length), (Status::Deadlock, Some(4)));
    // A state whose only successor is itself isn't deadlocked.
    let outcome = run(SPEC, "SPECIFICATION Spec", System { init: vec![0], next: diamond });
    assert_eq!(outcome.status, Status::Success);
}

#[test]
fn reports_the_invariant_a_state_violates() {
    let body = format!("{SPEC}\nSmall == x < 2\nPositive == x > 0");
    let config = "SPECIFICATION Spec\nINVARIANT Small";
    let outcome = run(&body, config, System { init: vec![0], next: counter });
    assert_eq!(outcome.status, Status::InvariantViolation);
    assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Small"), Some(3)));
    let config = "SPECIFICATION Spec\nINVARIANT Positive";
    let outcome = run(&body, config, System { init: vec![0], next: counter });
    assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Positive"), Some(1)));
}

#[test]
fn leaves_out_states_the_constraints_exclude() {
    let body = format!("{SPEC}\nBelow == x < 2\nStep == x' - x = 1");
    let config = "SPECIFICATION Spec\nCONSTRAINT Below";
    let outcome = run(&body, config, System { init: vec![0], next: counter });
    // State 2 is generated but neither stored nor expanded, so nothing deadlocks.
    assert_eq!(counts(&outcome), (Status::Success, Some(3), Some(2), Some(2)));
    let outcome = run(
        &body,
        "SPECIFICATION Spec\nACTION_CONSTRAINT Step\nCONSTRAINT Below",
        System { init: vec![0], next: |x| vec![x + 2, x + 1] },
    );
    assert_eq!(counts(&outcome), (Status::Success, Some(5), Some(2), Some(2)));
}

#[test]
fn checks_implied_actions_and_initial_predicates() {
    let body = format!("{SPEC}\nUp == [][x' > x]_x\nStart == x = 0\nAlways == []Start");
    let config = "SPECIFICATION Spec\nPROPERTY Up\nCHECK_DEADLOCK FALSE";
    let outcome = run(&body, config, System { init: vec![0], next: |x| vec![(x + 1) % 3] });
    assert_eq!(outcome.status, Status::LivenessViolation);
    assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Up"), Some(4)));
    let config = "SPECIFICATION Spec\nPROPERTY Start\nCHECK_DEADLOCK FALSE";
    let outcome = run(&body, config, System { init: vec![1], next: counter });
    assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Start"), Some(1)));
    // []P of a state predicate is an invariant, named by P.
    let config = "SPECIFICATION Spec\nPROPERTY Always\nCHECK_DEADLOCK FALSE";
    let outcome = run(&body, config, System { init: vec![0], next: counter });
    assert_eq!(outcome.status, Status::InvariantViolation);
    assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Start"), Some(2)));
}

#[test]
fn answers_tlcget_like_tlc() {
    let body = format!("{SPEC}\nShallow == TLCGet(\"level\") < 3\nFew == TLCGet(\"distinct\") < 3");
    let config = "SPECIFICATION Spec\nINVARIANT Shallow\nCHECK_DEADLOCK FALSE";
    let outcome = run(&body, config, System { init: vec![0], next: counter });
    assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Shallow"), Some(3)));
    let config = "SPECIFICATION Spec\nINVARIANT Few\nCHECK_DEADLOCK FALSE";
    let outcome = run(&body, config, System { init: vec![0], next: counter });
    assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Few"), Some(4)));
}
