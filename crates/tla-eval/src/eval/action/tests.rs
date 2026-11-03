use std::collections::{HashSet, VecDeque};
use std::hash::{DefaultHasher, Hasher};
use std::sync::Arc;

use tla_resolve::{DefId, RootName};

use crate::{ConstBinding, EvalError, Evaluator, State, Value};

fn evaluator_with(source: &str, constants: Vec<ConstBinding>) -> Evaluator {
    let spec = tla_resolve::resolve(source, &mut |_name: &str| None).unwrap_or_else(|error| {
        panic!("{error}");
    });
    Evaluator::new(Arc::new(spec), constants)
}

fn evaluator(source: &str) -> Evaluator {
    evaluator_with(source, Vec::new())
}

fn def(evaluator: &Evaluator, name: &str) -> DefId {
    match evaluator.spec.lookup(name) {
        Some(RootName::Def(id)) => id,
        other => panic!("{name} is {other:?}"),
    }
}

fn printed(state: &State) -> String {
    state.iter().map(Value::to_string).collect::<Vec<_>>().join(", ")
}

fn init_states(evaluator: &Evaluator, init: &str) -> Result<Vec<String>, EvalError> {
    let mut states = Vec::new();
    evaluator.init_states(&[def(evaluator, init)], &mut |state| {
        states.push(printed(&state));
        Ok(true)
    })?;
    Ok(states)
}

fn next_states(evaluator: &Evaluator, next: &str, state: &State) -> Result<Vec<String>, EvalError> {
    let mut states = Vec::new();
    evaluator.next_states(def(evaluator, next), state, &mut |state| {
        states.push(printed(&state));
        Ok(true)
    })?;
    Ok(states)
}

fn fingerprint(state: &State) -> u64 {
    let mut hasher = DefaultHasher::new();
    for value in state.iter() {
        value.fingerprint(&mut hasher).unwrap();
    }
    hasher.finish()
}

/// The states generated and the distinct states of a breadth-first search, as TLC counts them.
fn explore(evaluator: &Evaluator, init: &str, next: &str) -> (usize, usize) {
    let (mut generated, mut seen, mut queue) = (0, HashSet::new(), VecDeque::new());
    evaluator
        .init_states(&[def(evaluator, init)], &mut |state| {
            generated += 1;
            if seen.insert(fingerprint(&state)) {
                queue.push_back(state);
            }
            Ok(true)
        })
        .unwrap();
    let next = def(evaluator, next);
    while let Some(state) = queue.pop_front() {
        evaluator
            .next_states(next, &state, &mut |successor| {
                generated += 1;
                if seen.insert(fingerprint(&successor)) {
                    queue.push_back(successor);
                }
                Ok(true)
            })
            .unwrap();
    }
    (generated, seen.len())
}

fn state(values: Vec<Value>) -> State {
    values.into()
}

const COUNTER: &str = r#"
---- MODULE Counter ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y \in {1, 2}
Next == \/ x < 2 /\ x' = x + 1 /\ UNCHANGED y
        \/ y' = 3 /\ x' = x
====
"#;

#[test]
fn enumerates_initial_states_in_tlc_order() {
    let evaluator = evaluator(COUNTER);
    assert_eq!(init_states(&evaluator, "Init").unwrap(), ["0, 1", "0, 2"]);
}

#[test]
fn enumerates_successors_disjunct_by_disjunct() {
    let evaluator = evaluator(COUNTER);
    let current = state(vec![Value::Int(1), Value::Int(1)]);
    assert_eq!(next_states(&evaluator, "Next", &current).unwrap(), ["2, 1", "1, 3"]);
    let last = state(vec![Value::Int(2), Value::Int(1)]);
    assert_eq!(next_states(&evaluator, "Next", &last).unwrap(), ["2, 3"]);
}

#[test]
fn stops_when_asked() {
    let evaluator = evaluator(COUNTER);
    let mut seen = Vec::new();
    evaluator
        .init_states(&[def(&evaluator, "Init")], &mut |state| {
            seen.push(printed(&state));
            Ok(false)
        })
        .unwrap();
    assert_eq!(seen, ["0, 1"]);
}

/// The DieHard spec of tlaplus/Examples, which TLC explores to 97 states generated and 16
/// distinct.
const DIE_HARD: &str = r#"
---- MODULE DieHard ----
EXTENDS Naturals
VARIABLES big, small
Init == /\ big = 0
        /\ small = 0
FillSmallJug  == /\ small' = 3
                 /\ big' = big
FillBigJug    == /\ big' = 5
                 /\ small' = small
EmptySmallJug == /\ small' = 0
                 /\ big' = big
EmptyBigJug   == /\ big' = 0
                 /\ small' = small
Min(m,n) == IF m < n THEN m ELSE n
SmallToBig == /\ big'   = Min(big + small, 5)
              /\ small' = small - (big' - big)
BigToSmall == /\ small' = Min(big + small, 3)
              /\ big'   = big - (small' - small)
Next ==  \/ FillSmallJug
         \/ FillBigJug
         \/ EmptySmallJug
         \/ EmptyBigJug
         \/ SmallToBig
         \/ BigToSmall
====
"#;

#[test]
fn explores_die_hard_as_tlc_does() {
    assert_eq!(explore(&evaluator(DIE_HARD), "Init", "Next"), (97, 16));
}

/// TCommit of tlaplus/Examples with three resource managers, which TLC explores to 94 states
/// generated and 34 distinct.
const TCOMMIT: &str = r#"
---- MODULE TCommit ----
CONSTANT RM
VARIABLE rmState
TCInit ==   rmState = [rm \in RM |-> "working"]
canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
notCommitted == \A rm \in RM : rmState[rm] # "committed"
Prepare(rm) == /\ rmState[rm] = "working"
               /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
Decide(rm)  == \/ /\ rmState[rm] = "prepared"
                  /\ canCommit
                  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
               \/ /\ rmState[rm] \in {"working", "prepared"}
                  /\ notCommitted
                  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
TCNext == \E rm \in RM : Prepare(rm) \/ Decide(rm)
====
"#;

fn managers() -> Vec<ConstBinding> {
    let names = ["r1", "r2", "r3"].map(Value::model);
    vec![ConstBinding::Value(Value::set(names.to_vec()).unwrap())]
}

#[test]
fn explores_tcommit_as_tlc_does() {
    assert_eq!(explore(&evaluator_with(TCOMMIT, managers()), "TCInit", "TCNext"), (94, 34));
}

/// TwoPhase of tlaplus/Examples with three resource managers, which TLC explores to 1146 states
/// generated and 288 distinct.
const TWO_PHASE: &str = r#"
---- MODULE TwoPhase ----
CONSTANT RM
VARIABLES rmState, tmState, tmPrepared, msgs
TPInit ==
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}
TMRcvPrepared(rm) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>
TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>
TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>
RMPrepare(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>
RMChooseToAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
RMRcvCommitMsg(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
RMRcvAbortMsg(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
TPNext ==
  \/ TMCommit \/ TMAbort
  \/ \E rm \in RM :
       TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)
====
"#;

#[test]
fn explores_two_phase_as_tlc_does() {
    assert_eq!(explore(&evaluator_with(TWO_PHASE, managers()), "TPInit", "TPNext"), (1146, 288));
}

/// DiningPhilosophers of tlaplus/Examples with five philosophers, which TLC explores to 174
/// states generated and 58 distinct, checking `ENABLED Next` as an invariant.
const DINING: &str = r#"
---- MODULE DiningPhilosophers ----
EXTENDS Naturals, FiniteSets
CONSTANT N
P == 1..N
LeftFork(p) == p
RightFork(p) == (p % N) + 1
VARIABLES philosophers, forks
Init ==
    /\ philosophers = [ p \in P |-> {} ]
    /\ forks = 1..N
TakeLeft(p) ==
    /\ p % 2 = 0 => philosophers[p] = {RightFork(p)}
    /\ LeftFork(p) \in forks
    /\ forks' = forks \ {LeftFork(p)}
    /\ philosophers' =
        [philosophers EXCEPT ![p] = philosophers[p] \cup {LeftFork(p)}]
TakeRight(p) ==
    /\ p % 2 = 1 => philosophers[p] = {LeftFork(p)}
    /\ RightFork(p) \in forks
    /\ forks' = forks \ {RightFork(p)}
    /\ philosophers' =
        [philosophers EXCEPT ![p] = philosophers[p] \cup {RightFork(p)}]
Release(p) ==
    /\ philosophers[p] = {LeftFork(p), RightFork(p)}
    /\ forks' = forks \cup {LeftFork(p), RightFork(p)}
    /\ philosophers' = [philosophers EXCEPT ![p] = {}]
Next ==
    \E p \in P:
        \/ TakeLeft(p)
        \/ TakeRight(p)
        \/ Release(p)
NoDeadlock == ENABLED Next
====
"#;

#[test]
fn explores_dining_philosophers_as_tlc_does() {
    let evaluator = evaluator_with(DINING, vec![ConstBinding::Value(Value::Int(5))]);
    assert_eq!(explore(&evaluator, "Init", "Next"), (174, 58));
    let mut initial = Vec::new();
    evaluator
        .init_states(&[def(&evaluator, "Init")], &mut |state| {
            initial.push(state);
            Ok(true)
        })
        .unwrap();
    let enabled = evaluator.eval_def(def(&evaluator, "NoDeadlock"), Some(&initial[0])).unwrap();
    assert_eq!(enabled.to_string(), "TRUE");
}

const ACTIONS: &str = r#"
---- MODULE Actions ----
EXTENDS Naturals
VARIABLES x, y
Inc(c) == c' = c + 1
Both(A, B) == A /\ B
Parameterized == Inc(x) /\ UNCHANGED y
Arguments == Both(x' = 1, y' = x' + 1)
Branching == x' = 1 /\ (TRUE \/ TRUE) /\ y' = 2
Settled == x' = 1 /\ y' = 2 /\ (TRUE \/ TRUE)
Box == [x' = x + 1 /\ y' = y]_<<x, y>>
Angle == <<x' = 5>>_x /\ y' = y
Ordered == \E v \in {3, 1, 2} : x' = v /\ y' = y
Members == x' \in {3, 1} /\ y' \in {7, 6}
Subsets == x' \subseteq {1, 2} /\ y' = y
PrimedExpression == x' = 1 /\ y' = 2 /\ (x + y)' = 3
Let == LET z == x + 10 IN x' = z /\ y' = y
If == IF x = 0 THEN x' = 1 /\ y' = y ELSE UNCHANGED <<x, y>>
Case == CASE x = 0 -> x' = 5 /\ y' = y [] OTHER -> UNCHANGED <<x, y>>
Forall == \A v \in {4} : x' = v /\ y' = v
Conflicting == \A v \in {1, 2} : x' = v /\ y' = y
Implication == (x = 0 => x' = 9) /\ x' \in {9, 8} /\ y' = y
InitFiltered == x \in {1, 2, 3} /\ y = x + 1 /\ x # 2
InitExists == \E v \in {1, 2} : x = v /\ y = v * 10
====
"#;

fn successors(name: &str, x: i32, y: i32) -> Vec<String> {
    next_states(&evaluator(ACTIONS), name, &state(vec![Value::Int(x), Value::Int(y)])).unwrap()
}

#[test]
fn walks_into_definitions_and_their_arguments() {
    assert_eq!(successors("Parameterized", 0, 7), ["1, 7"]);
    assert_eq!(successors("Arguments", 0, 0), ["1, 2"]);
    assert_eq!(successors("Let", 1, 2), ["11, 2"]);
    assert_eq!(successors("If", 0, 2), ["1, 2"]);
    assert_eq!(successors("If", 3, 2), ["3, 2"]);
    assert_eq!(successors("Case", 0, 2), ["5, 2"]);
    assert_eq!(successors("Case", 1, 2), ["1, 2"]);
    assert_eq!(successors("Implication", 0, 0), ["9, 0"]);
    assert_eq!(successors("Implication", 1, 0), ["8, 0", "9, 0"]);
}

/// Once every variable has a value, TLC evaluates the conjuncts left as predicates, so only a
/// disjunction met before that yields a successor for each disjunct.
#[test]
fn branches_until_every_variable_has_a_value() {
    assert_eq!(successors("Branching", 0, 0), ["1, 2", "1, 2"]);
    assert_eq!(successors("Settled", 0, 0), ["1, 2"]);
    assert_eq!(successors("PrimedExpression", 0, 0), ["1, 2"]);
}

#[test]
fn enumerates_choices_in_tlc_order() {
    assert_eq!(successors("Ordered", 0, 0), ["1, 0", "2, 0", "3, 0"]);
    assert_eq!(successors("Members", 0, 0), ["1, 6", "1, 7", "3, 6", "3, 7"]);
    assert_eq!(successors("Subsets", 0, 5), ["{}, 5", "{1}, 5", "{2}, 5", "{1, 2}, 5"]);
    assert_eq!(successors("Forall", 0, 0), ["4, 4"]);
    assert!(successors("Conflicting", 0, 0).is_empty());
}

#[test]
fn walks_subscripted_actions() {
    assert_eq!(successors("Box", 1, 2), ["2, 2", "1, 2"]);
    assert_eq!(successors("Angle", 1, 2), ["5, 2"]);
    assert!(successors("Angle", 5, 2).is_empty());
}

#[test]
fn filters_initial_states_by_later_conjuncts() {
    let evaluator = evaluator(ACTIONS);
    assert_eq!(init_states(&evaluator, "InitFiltered").unwrap(), ["1, 2", "3, 4"]);
    assert_eq!(init_states(&evaluator, "InitExists").unwrap(), ["1, 10", "2, 20"]);
}

const INNER: &str = r#"
---- MODULE Inner ----
EXTENDS Naturals
VARIABLE v
Step == v' = v + 1
====
"#;

#[test]
fn walks_actions_of_instances() {
    let source = r#"
---- MODULE Outer ----
VARIABLES x, y
I == INSTANCE Inner WITH v <- x
P(w) == INSTANCE Inner WITH v <- w
Named == I!Step /\ UNCHANGED y
Parameterized == P(y)!Step /\ UNCHANGED x
====
"#;
    let spec =
        tla_resolve::resolve(source, &mut |name: &str| (name == "Inner").then(|| INNER.to_owned()))
            .unwrap();
    let evaluator = Evaluator::new(Arc::new(spec), Vec::new());
    let current = state(vec![Value::Int(1), Value::Int(5)]);
    assert_eq!(next_states(&evaluator, "Named", &current).unwrap(), ["2, 5"]);
    assert_eq!(next_states(&evaluator, "Parameterized", &current).unwrap(), ["1, 6"]);
}

const ERRORS: &str = r#"
---- MODULE Errors ----
EXTENDS Naturals
VARIABLES x, y
A == x' = 1
Next == A \/ (x' = 2 /\ y' = 3)
Partial == x' = 1
InitPartial == x = 1
Literal == 3 /\ x' = 1 /\ y' = 1
Late == x' = 1 /\ y' = 1 /\ 3
If == IF 1 THEN x' = 1 ELSE x' = 2
Infinite == x' \in Nat /\ y' = y
InitUnchanged == UNCHANGED x
Early == y' = x' /\ x' = 1
====
"#;

fn error(name: &str) -> EvalError {
    let evaluator = evaluator(ERRORS);
    next_states(&evaluator, name, &state(vec![Value::Int(0), Value::Int(0)])).unwrap_err()
}

/// tla-ts's successors.ts: TLC's errors for the states it can't complete.
#[test]
fn reports_incomplete_states_with_the_partial_state() {
    let next = error("Next");
    assert_eq!(
        next.message,
        "Successor state is not completely specified by action A of the next-state relation. The following variable is not defined: y."
    );
    let incomplete = next.incomplete.unwrap();
    assert_eq!(incomplete.action.map(|name| name.as_str()), Some("A"));
    assert_eq!(incomplete.missing.len(), 1);
    assert_eq!(incomplete.state, [Some("1".to_owned()), None]);
    assert!(
        error("Partial")
            .message
            .starts_with("Successor state is not completely specified by the next-state action.")
    );
    let evaluator = evaluator(ERRORS);
    let init = init_states(&evaluator, "InitPartial").unwrap_err();
    assert_eq!(init.message, "current state is not a legal state");
    assert_eq!(init.incomplete.unwrap().state, [Some("1".to_owned()), None]);
}

#[test]
fn words_errors_as_tlc_does() {
    assert_eq!(error("Literal").message, "The next state relation is not a boolean expression.\n3");
    assert_eq!(
        error("Late").message,
        "In computing next states, TLC expected a boolean expression,\nbut instead found 3.\n3"
    );
    assert_eq!(
        error("If").message,
        "In computing next states, a non-boolean expression (an integer) was used as the condition of an IF.line 11, col 7 to line 11, col 34 of module Errors"
    );
    assert_eq!(
        error("Infinite").message,
        "In computing next states, the right side of \\IN is not enumerable.\nline 12, col 13 to line 12, col 22 of module Errors"
    );
    assert_eq!(
        error("Early").message,
        "In evaluation, the identifier x is either undefined or not an operator.\nline 14, col 15 to line 14, col 15 of module Errors"
    );
    let evaluator = evaluator(ERRORS);
    assert_eq!(
        init_states(&evaluator, "InitUnchanged").unwrap_err().message,
        "UNCHANGED appears in an initial predicate at line 13, column 18"
    );
}

const FUNCTION_ACTIONS: &str = r#"
---- MODULE FunctionActions ----
VARIABLES x, y
Actions == [p \in {1, 2} |-> x' = p /\ y' = y]
Steps[n \in {1, 2}] == x' = n /\ y' = n
One == Actions[1]
Each == \E p \in {2, 1} : Actions[p]
Defined == Steps[2]
Guard == <<TRUE, FALSE>>[1] /\ x' = x /\ y' = y
Outside == Actions[3]
NotBoolean == <<1>>[1] /\ x' = x /\ y' = y
NotFunction == {1}[1] /\ x' = x /\ y' = y
====
"#;

/// tla-ts's compileFunctionAction: TLC walks the body of a lazy function an action applies, at
/// the argument, so each disjunct or witness inside it generates a state.
#[test]
fn walks_the_bodies_of_functions_of_actions() {
    let evaluator = evaluator(FUNCTION_ACTIONS);
    let current = state(vec![Value::Int(0), Value::Int(0)]);
    let successors = |name| next_states(&evaluator, name, &current);
    assert_eq!(successors("One").unwrap(), ["1, 0"]);
    assert_eq!(successors("Each").unwrap(), ["1, 0", "2, 0"]);
    assert_eq!(successors("Defined").unwrap(), ["2, 2"]);
    assert_eq!(successors("Guard").unwrap(), ["0, 0"]);
    assert!(successors("Outside").unwrap_err().message.starts_with("In applying the function\n"));
    assert_eq!(
        successors("NotBoolean").unwrap_err().message,
        "In computing next states, TLC expected a boolean expression,\nbut didn't find one.\nline 11, col 15 to line 11, col 22 of module FunctionActions"
    );
    assert_eq!(
        successors("NotFunction").unwrap_err().message,
        "In computing next states, a non-function (a set of the form {e1, ... ,eN}) was applied as a function.\nline 12, col 16 to line 12, col 21 of module FunctionActions"
    );
}

/// The states generated and distinct of a spec with `body` after `EXTENDS Naturals, FiniteSets`.
fn explore_body(body: &str) -> (usize, usize) {
    let source = format!("---- MODULE M ----\nEXTENDS Naturals, FiniteSets\n{body}\n====");
    explore(&evaluator(&source), "Init", "Next")
}

#[test]
fn streams_lazy_unions_with_their_duplicates() {
    let records = "x' \\in [b : UNION {{3, 1}, 0..1}, a : UNION {{2}, 1..2}]";
    assert_eq!(explore_body(&format!("VARIABLE x\nInit == x = 0\nNext == {records}")).0, 85);
    let set = "UNION {SUBSET {1}, {{}}}";
    let body = format!("VARIABLE x\nInit == x \\in {set}\nNext == x' \\in {set}");
    assert_eq!(explore_body(&body), (9, 2));
    let counts =
        |set: &str| explore_body(&format!("VARIABLE x\nInit == x \\in {set}\nNext == UNCHANGED x"));
    assert_eq!(counts("SUBSET {1} \\cup SUBSET {2}"), (7, 3));
    assert_eq!(counts("(1..3) \\cup SUBSET {}"), (8, 4));
    assert_eq!(counts("{1} \\cup {1, 2}"), (4, 2));
    assert_eq!(counts("UNION UNION (SUBSET {{}, {{}}})"), (3, 1));
    assert_eq!(counts("UNION UNION {SUBSET {1}, {{1}}}"), (3, 1));
    let nested = "x = 0 /\\ x' \\in UNION UNION (SUBSET {{1}, {1, 2}})";
    assert_eq!(explore_body(&format!("VARIABLE x\nInit == x = 0\nNext == {nested}")), (7, 3));
}

#[test]
fn streams_a_union_until_tlc_caches_it() {
    let generated = |next: &str| {
        let body =
            format!("VARIABLES x, y\nInit == x = 0 /\\ y = 0\nNext == ({next}) /\\ UNCHANGED x");
        explore_body(&body).0
    };
    let union = "UNION {UNION {0..2, {1}}, {7}}";
    assert_eq!(generated(&format!("y' \\in {union}")), 21);
    assert_eq!(generated(&format!("\\E e \\in {union} : y' = e")), 17);
    assert_eq!(generated("y' \\in {1} \\X UNION {UNION {0..2, {1}}, {1, 2}}"), 25);
    // A LET definition is evaluated anew at each reference, so sizing it leaves the next uncached.
    assert_eq!(generated(&format!("LET u == {union} IN Cardinality(u) > 0 /\\ y' \\in u")), 21);
    // Sizing the set itself caches it.
    let sized = "\\E u \\in {UNION {0..2, {1}}} : Cardinality(u) > 0 /\\ y' \\in UNION {u, {7}}";
    assert_eq!(generated(sized), 17);
    // An argument keeps its value until the walk assigns a variable.
    let call = |body: &str| {
        let body = format!(
            "VARIABLES x, y\nInit == x = 0 /\\ y = 0\nOp(u) == {body}\nNext == Op({union})"
        );
        explore_body(&body).0
    };
    assert_eq!(call("Cardinality(u) > 0 /\\ y' \\in u /\\ UNCHANGED x"), 17);
    assert_eq!(call("Cardinality(u) > 0 /\\ UNCHANGED x /\\ y' \\in u"), 21);
    // Sorting a set enumeration compares each element after the first, which caches it.
    let counts =
        |set: &str| explore_body(&format!("VARIABLE x\nInit == x \\in {set}\nNext == UNCHANGED x"));
    assert_eq!(counts("UNION {UNION (SUBSET {{1}, {1, 2}}), {1}}"), (8, 3));
    assert_eq!(counts("UNION {{1}, UNION (SUBSET {{1}, {1, 2}})}"), (6, 3));
}
