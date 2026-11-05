use crate::Status;
use crate::search::Ending;
use tla_tools_eval::{State, Value};

use crate::testing::{System, explore, run, spec, spec_extending};

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
    // A new state counts as distinct before TLC checks its invariants, so the third state
    // sees three.
    let config = "SPECIFICATION Spec\nINVARIANT Few\nCHECK_DEADLOCK FALSE";
    let outcome = run(&body, config, System { init: vec![0], next: counter });
    assert_eq!((outcome.violation.as_deref(), outcome.trace_length), (Some("Few"), Some(3)));
    // TLC stops between expansions once `TLCSet("exit", TRUE)` is evaluated.
    let body = format!("{SPEC}\nStop == TLCSet(\"exit\", TLCGet(\"distinct\") > 1)");
    let config = "SPECIFICATION Spec\nINVARIANT Stop\nCHECK_DEADLOCK FALSE";
    let outcome = run(&body, config, System { init: vec![0], next: counter });
    assert_eq!(counts(&outcome), (Status::Success, Some(2), Some(2), Some(2)));
}

#[test]
fn rebuilds_the_behavior_to_a_violation() {
    let body = format!("{SPEC}\nSmall == x < 2");
    let config = "SPECIFICATION Spec\nINVARIANT Small";
    let searched = explore(spec(&body), config, System { init: vec![0], next: counter });
    assert_eq!(searched.trace_length, 3);
    assert_eq!(xs(&searched.trace), vec![0, 1, 2]);
    // A deadlock ends in the state without successors.
    let searched =
        explore(spec(SPEC), "SPECIFICATION Spec", System { init: vec![0], next: counter });
    assert_eq!((searched.trace_length, searched.trace.len()), (4, 4));
}

#[test]
fn keeps_states_for_trace() {
    let body = format!("{SPEC}\nShort == Len(Trace) < 3");
    let config = "SPECIFICATION Spec\nINVARIANT Short";
    let spec = spec_extending("Naturals, Sequences, TLC, TLCExt", &body);
    let searched = explore(spec, config, System { init: vec![0], next: counter });
    assert_eq!(searched.ending, Ending::InvariantViolation("Short".into()));
    assert_eq!(xs(&searched.trace), vec![0, 1, 2]);
}

/// The values of `x` along a behavior.
fn xs(behavior: &[State]) -> Vec<i32> {
    behavior
        .iter()
        .map(|state| match state[0] {
            Value::Int(x) => x,
            _ => panic!("x is an integer"),
        })
        .collect()
}
