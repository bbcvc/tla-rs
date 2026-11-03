//! Expressions that read a state, and actions that read a step from one state to the next.

mod common;

use common::{def, evaluator, evaluator_with, int, ints, state};
use tla_eval::{Evaluator, State, Value};

fn in_state(evaluator: &Evaluator, name: &str, current: &State) -> String {
    match evaluator.eval_def(def(evaluator, name), Some(current)) {
        Ok(value) => value.to_string(),
        Err(error) => panic!("{name}: {error}"),
    }
}

fn on_step(evaluator: &Evaluator, name: &str, current: &State, next: &State) -> String {
    match evaluator.eval_action(def(evaluator, name), current, next) {
        Ok(value) => value.to_string(),
        Err(error) => panic!("{name}: {error}"),
    }
}

#[test]
fn reads_variables_in_the_current_state() {
    let evaluator = evaluator(
        r#"
VARIABLES x, y
Pair == <<x, y>>
TypeOK == x \in {1, 2} /\ y \in SUBSET {1, 2}
Twice(v) == <<v, v>>
Called == Twice(x)
"#,
    );
    let current = state(vec![int(1), ints(&[2])]);
    assert_eq!(in_state(&evaluator, "Pair", &current), "<<1, {2}>>");
    assert_eq!(in_state(&evaluator, "TypeOK", &current), "TRUE");
    assert_eq!(in_state(&evaluator, "Called", &current), "<<1, 1>>");
    assert_eq!(
        evaluator.eval_def(def(&evaluator, "Pair"), None).unwrap_err().message,
        "In evaluation, the identifier x is either undefined or not an operator."
    );
}

#[test]
fn reads_primed_expressions_in_the_next_state() {
    let evaluator = evaluator(
        r#"
VARIABLES x, y
Swap == x' = y /\ y' = x
Stutter == UNCHANGED <<x, y>>
Primed == <<x', (x \cup y)', x>>
Same(v) == v' = v
KeepsX == Same(x)
LetPrimed == LET sum == x \cup y IN sum'
"#,
    );
    let current = state(vec![ints(&[1]), ints(&[2])]);
    let swapped = state(vec![ints(&[2]), ints(&[1])]);
    assert_eq!(on_step(&evaluator, "Swap", &current, &swapped), "TRUE");
    assert_eq!(on_step(&evaluator, "Swap", &current, &current), "FALSE");
    assert_eq!(on_step(&evaluator, "Stutter", &current, &current), "TRUE");
    assert_eq!(on_step(&evaluator, "Stutter", &current, &swapped), "FALSE");
    assert_eq!(on_step(&evaluator, "Primed", &current, &swapped), "<<{2}, {1, 2}, {1}>>");
    assert_eq!(on_step(&evaluator, "KeepsX", &current, &current), "TRUE");
    assert_eq!(on_step(&evaluator, "KeepsX", &current, &swapped), "FALSE");
    assert_eq!(on_step(&evaluator, "LetPrimed", &current, &swapped), "{1, 2}");
    assert_eq!(
        evaluator.eval_def(def(&evaluator, "Swap"), Some(&current)).unwrap_err().message,
        "A primed expression appears outside an action"
    );
}

#[test]
fn evaluates_actions_with_subscripts() {
    let evaluator = evaluator(
        r#"
VARIABLE x
Box == [x' # x]_x
Angle == <<x' = x>>_x
Moves == <<x' # x>>_x
"#,
    );
    let current = state(vec![int(1)]);
    let changed = state(vec![int(2)]);
    assert_eq!(on_step(&evaluator, "Box", &current, &current), "TRUE");
    assert_eq!(on_step(&evaluator, "Box", &current, &changed), "TRUE");
    assert_eq!(on_step(&evaluator, "Angle", &current, &current), "FALSE");
    assert_eq!(on_step(&evaluator, "Moves", &current, &changed), "TRUE");
}

const COUNTER: &str = r#"
---- MODULE Counter ----
VARIABLE count
Values == {count}
Step == count' = Values
Keep == UNCHANGED count
====
"#;

#[test]
fn substitutes_variables_of_instances() {
    let evaluator = evaluator_with(
        r#"
VARIABLES x, y
X == INSTANCE Counter WITH count <- x
C(v) == INSTANCE Counter WITH count <- v
Unnamed(v) == LET Inner == INSTANCE Counter WITH count <- v IN Inner!Keep
Steps == <<X!Step, C(y)!Step, X!Keep, Unnamed(y)>>
Reads == C(x)!Values
"#,
        &[("Counter", COUNTER)],
        Vec::new(),
    );
    let empty = Value::empty_set();
    let nested = |value: Value| Value::set(vec![value]).unwrap();
    let current = state(vec![nested(empty.clone()), empty.clone()]);
    let next = state(vec![nested(nested(empty.clone())), empty]);
    assert_eq!(on_step(&evaluator, "Steps", &current, &next), "<<TRUE, FALSE, FALSE, TRUE>>");
    assert_eq!(in_state(&evaluator, "Reads", &current), "{{{}}}");
}

#[test]
fn keeps_the_states_a_lazy_value_was_built_in() {
    let evaluator = evaluator(
        r#"
VARIABLE x
Later == {s \in STRING : s = x}
Matches == "a" \in Later
"#,
    );
    let current = state(vec![Value::str("a")]);
    assert_eq!(in_state(&evaluator, "Matches", &current), "TRUE");
    let later = evaluator.eval_def(def(&evaluator, "Later"), Some(&current)).unwrap();
    assert!(later.contains(&Value::str("a")).unwrap());
    assert!(!later.contains(&Value::str("b")).unwrap());
}
