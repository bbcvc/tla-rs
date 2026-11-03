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
