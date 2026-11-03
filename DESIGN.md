# tla-rs Design & Development Plan

> [EVALUATION.md](EVALUATION.md) revises parts of this plan. Where the two conflict, EVALUATION.md wins.

## 1. Project Overview and Core Goals

### 1.1 Vision

Build **`tla-rs`** — a TLA+ interpreter and explicit-state model checker with zero JVM dependency, a compact memory footprint, and lock-free multi-core concurrency. While staying 100% semantically consistent with the official Java **TLC** and **`tla-ts`**, it should deliver verification throughput **5–10x** faster than `tla-ts` and **10–20x** faster than the original TLC, and it should compile to both a native CLI and WebAssembly.

### 1.2 Core Acceptance Criteria (Definition of Done)

1. **Semantic consistency**: Pass 100% of the **542 official conformance test models (Conformance Suite)** extracted by `tla-ts`. For every model, the `Status` (result status) and `Distinct States` (number of unique states) must match the original TLC exactly.
2. **CLI and interface compatibility**: Run checks directly from `.tla` and `.cfg` files, with output format aligned to TLC and `tla-ts`.
3. **Performance targets**: In single-threaded and 8-thread benchmarks (Two-Phase Commit, Raft, Dining Philosophers), memory usage below 25% of TLC's, and wall-clock time below 25% of `tla-ts`'s.

---

## 2. System Architecture and Cargo Workspace Layout

The project uses a decoupled multi-crate `Cargo Workspace` architecture and strictly follows the one-way dependency principle (compiled bottom-up):

```text
tla-rs/
├── Cargo.toml                  # Workspace root config and unified dependency versions
├── crates/
│   ├── tla-intern/             # [Foundation] String and symbol interning pool (Symbol Interner)
│   ├── tla-ast/                # [Syntax] Pure AST data structures, Span location info, Config structs
│   ├── tla-parser/             # [Frontend] CST->AST lowering based on tree-sitter-tlaplus, and .cfg parsing
│   ├── tla-value/              # [Value system] TlaValue definition, canonicalization, 64-bit fingerprint hashing
│   ├── tla-eval/               # [Evaluation] Expression evaluator, primed-variable successor enumeration, built-in standard library
│   ├── tla-checker/            # [Engine] Single-/multi-threaded BFS state-graph search, deadlock/invariant/liveness checking
│   └── tla-cli/                # [Entry point] Command-line tool and JSON/DOT report export
└── tests/
    └── conformance/            # [Acceptance] Hosts the 542 standard models and golden-snapshot comparison scripts

```

### Core Third-Party Dependencies (Cargo.toml conventions)

| Area | Recommended Crate | Purpose |
| --- | --- | --- |
| **Parsing** | `tree-sitter`, `tree-sitter-tlaplus` | Reuse the mature community TLA+ grammar instead of hand-writing a 28k-line SANY parser |
| **Symbol interning** | `lasso` (multi-threaded `ThreadedRodeo`) | Turn every identifier into a 32-bit `Spur` ID so variable lookup becomes an `O(1)` array index |
| **Arbitrary-precision integers** | `num-bigint`, `num-traits` | The TLA+ spec requires integers that never overflow (arbitrary precision) |
| **Fast fingerprint hashing** | `xxhash-rust` (xxh3) or `rustc-hash` | Compute deterministic 64-bit fingerprints for states and sets |
| **Concurrent multi-core state table** | `dashmap`, `crossbeam-deque` | Lock-free concurrent storage of visited-state fingerprints (Visited Set) and work-stealing queues |
| **Errors and diagnostics** | `thiserror`, `miette` | Structured domain error definitions and error output with source line/column highlighting |

---

## 3. Core Engineering Rules (Non-Negotiable Design Laws)

The following 4 domain laws must be followed strictly when writing code; otherwise rework during later refactoring is guaranteed:

### Law 1: Enforce Value Canonicalization at Construction Time

TLA+ is an untyped set-theoretic language: **sequences (Tuple), records (Record), and functions (Function) are all functions semantically**.

* **Problem**: `<<"a", "b">>` and `[x \in 1..2 |-> IF x=1 THEN "a" ELSE "b"]` are exactly equal in TLA+ (`=` is `TRUE`).
* **Rule**: External code must never construct the `Value::Func` or `Value::Tuple` enum variants directly. They must be created through the smart constructor `Value::make_func(map)`: when it detects that the domain (keys) of `map` is exactly the contiguous integers `1` to `n`, it **must automatically collapse (normalize) it into `Value::Tuple`**. This is what guarantees that the fingerprints computed from Rust's `PartialEq` and `Hash` match TLC 100%.

### Law 2: Sets and Powersets Must Be Lazily Evaluated by Default

* **Problem**: TLA+ frequently contains `S \in SUBSET (1..100)` or `[1..10 -> Boolean]`. Expanding these eagerly would produce `2^100` elements and blow up memory instantly.
* **Rule**: `Value` must distinguish between **enumerable finite sets (normalized `BTreeSet<Value>`)** and **lazy sets (`Interval(min, max)`, `Powerset(base)`, `FuncSet(domain, range)`)**.
* When evaluating `x \in SUBSET S` (a membership test), do not expand the powerset; rewrite it directly as the check `x \subseteq S` (`O(|x|)` complexity).
* Only call `.iter_elements()` to expand the stream on demand for `CHOOSE x \in S`, `\A x \in S`, or when enumerating branches for a variable.

### Law 3: Two-Phase Environment Binding (Unprimed vs. Primed State)

* **Rule**: The evaluation context `EvalCtx` must contain two independent state slots:
  1. `curr_state: &State` (read-only, binds all ordinary variables such as `x`).
  2. `next_state: SmallVec<[Option<Value>; 16]>` (writable with backtracking, binds primed variables such as `x'`).
* When evaluating `x' = expr` or `x' \in S`:
  * If `next_state[x]` is `None`, the expression is an **assignment / branch-generating action**: write the computed value into `next_state[x]` and return `Value::Bool(true)` (for `\in S`, clone the context and iterate over `S` per branch).
  * If `next_state[x]` is already `Some(val)`, it degrades into an ordinary **equality / membership test**.

### Law 4: Double-Oracle Reference Strategy

* When deciding the simplest way to write architecture, data structures, or control flow, **consult `aidenybai/tla-ts`**.
* When operator precedence, odd set-comparison rules, or error boundaries are unclear, **consult `tlaplus/tlaplus` (the Java TLC source)**, or simply run a minimal reproduction case through TLC.

---

## 4. Phased Development Roadmap (5 Milestones)

Proceed through the following 5 phases (milestones), each with clear deliverables and a closed testing loop:

### Phase 1: Syntax Frontend and AST Lowering (estimated: 1 week / ~1,500 LOC)

* **Tasks**:
  1. Set up the Cargo Workspace and initialize `tla-intern` and `tla-ast`.
  2. Integrate `tree-sitter-tlaplus` in `tla-parser` and write a `lower_module()` function that recursively lowers Tree-sitter CST nodes into strongly typed `tla_ast::Module` and `tla_ast::Expr`.
  3. Implement the `.cfg` configuration file parser (supporting `INIT`, `NEXT`, `INVARIANT`, `CONSTANT`, `SYMMETRY`).
  4. Implement scope resolution: determine whether an identifier is a `Variable` (converted to a slot index `usize`), a `Constant`, a user-defined `Operator`, or a local variable.
* **Phase acceptance**: Able to parse complex files such as `Counter.tla` and `TwoPhase.tla` and print an AST free of syntax errors.

### Phase 2: Core Value System and Pure Expression Evaluator (estimated: 1.5 weeks / ~2,500 LOC)

* **Tasks**:
  1. In `tla-value`, implement the `Value` enum (`Bool`, `Int`, `Str`, `ModelValue`, `Tuple`, `Set`, `Func`, `Interval`, `Powerset`, `FuncSet`) along with the mandatory canonicalizing constructors.
  2. Implement `format_value(&Value) -> String` (strictly aligned with TLC's output format) and a deterministic `fingerprint(&self) -> u64`.
  3. In `tla-eval`, implement stateless pure expression evaluation `eval_expr(&ctx, &expr) -> Result<Value, TlaError>`.
  4. Implement the built-in standard modules: `Naturals`, `Integers`, `Sequences` (`Append`, `Head`, `Tail`, `SubSeq`, `Len`), `FiniteSets` (`Cardinality`, `IsFiniteSet`), `TLC` (`Print`, `Assert`, `:>` and `@@` function concatenation).
* **Phase acceptance**: Port all of `tla-ts`'s unit tests for `ASSUME` and constant-expression evaluation; 100% pass.

### Phase 3: Next-State Generation and Single-Threaded Model Checker (estimated: 2 weeks / ~2,500 LOC)

* **Tasks**:
  1. Implement the action relation evaluator (Action / Next-State Generator): support `/\` (conjunction passes partially bound state along), `\/` (disjunction merges multiple state branches), `\E x \in S` (existential quantifier branch expansion), and `UNCHANGED <<x, y>>`.
  2. Implement the solver for the set of `Init` initial states.
  3. Implement the single-threaded BFS main loop in `tla-checker`:
     * Use `FxHashMap<u64, Option<u64>>` to record `state fingerprint -> parent state fingerprint`.
     * For every newly generated state, first check that all `INVARIANT`s return `Bool(true)`.
     * If a state has no successors and deadlock checking is enabled, report `Deadlock` and reconstruct the full `Trace` by walking back along the parent-fingerprint chain.
* **Phase acceptance**: Successfully run `Counter`, `DiningPhilosophers`, `BoundedQueue`, and `TwoPhaseCommit`, with `Distinct states` counts exactly matching TLC.

### Phase 4: Module Instantiation (INSTANCE) and the 542-Model Conformance Push (estimated: 2–3 weeks / ~3,000 LOC)

* **Tasks**:
  1. Implement TLA+'s critically important module reuse mechanisms: `EXTENDS` and `LocalM == INSTANCE OtherModule WITH x <- expr`.
  2. Implement recursive operators (`RECURSIVE Op(_)`) and higher-order operators (lambda `LAMBDA x : expr`).
  3. Write the `tests/conformance` batch test runner that loads `tla-ts`'s 542 test models directly.
  4. **Failure-driven iteration**: Run all 542 models, group failures by error category, and fix edge-case operator semantics one by one until the pass rate reaches 95%+.
* **Phase acceptance**: In single-threaded mode, state counts and verdicts for all 542 conformance models are fully aligned.

### Phase 5: Lock-Free Multi-Core Concurrency and Temporal Liveness Checking (estimated: 2 weeks / ~2,000 LOC)

* **Tasks**:
  1. Upgrade the single-threaded BFS into a multi-core work-stealing engine based on `DashMap` + `crossbeam_deque`, supporting `--workers N`.
  2. (Optional, advanced) Implement temporal-logic liveness checking (Liveness: `[]<>P`, `<>[]P`, `WF_v(A)`, `SF_v(A)`): build the tableau product graph and run Tarjan's strongly connected components (SCC) algorithm to detect accepting cycles.
  3. Integrate `clap` to round out the CLI tool, and write benchmark scripts comparing against TLC and `tla-ts`.
* **Phase acceptance**: Run the `Raft` and `Fast Paxos` benchmarks on an 8-core machine, verifying that state counts remain 100% deterministic under multi-threading with no data races.

---

## 5. Core Data Structures and Key Algorithm Blueprints (ready to copy as starter code)

### 5.1 `tla-value`: A Value System and State Definition That Guarantee Semantic Equivalence

```rust
// crates/tla-value/src/lib.rs
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive};
use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use tla_intern::Spur;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Value {
    Bool(bool),
    Int(BigInt),
    Str(Arc<str>),
    ModelValue(Spur),
    /// Normalized sequence/tuple <<v1, v2, ...>> (1-based indexing)
    Tuple(Arc<[Value]>),
    /// Normalized explicit finite set {v1, v2, ...}
    Set(Arc<BTreeSet<Value>>),
    /// Normalized function/record (note: if the domain is the contiguous integers 1..n,
    /// it has already been converted to a Tuple at construction time)
    Func(Arc<BTreeMap<Value, Value>>),
    /// Lazy integer interval min..max
    Interval(BigInt, BigInt),
    /// Lazy powerset SUBSET S
    Powerset(Arc<Value>),
    /// Lazy function set [domain -> range]
    FuncSet(Arc<Value>, Arc<Value>),
}

impl Value {
    /// Smart constructor: ensures any function whose domain is 1..=n is automatically normalized to a Tuple
    pub fn make_func(map: BTreeMap<Value, Value>) -> Self {
        if map.is_empty() {
            return Value::Tuple(Arc::from([]));
        }
        let n = map.len();
        let is_one_based_seq = map.keys().enumerate().all(|(idx, k)| {
            matches!(k, Value::Int(i) if i.to_usize() == Some(idx + 1))
        });

        if is_one_based_seq {
            let vec: Vec<Value> = map.into_values().collect();
            Value::Tuple(Arc::from(vec))
        } else {
            Value::Func(Arc::new(map))
        }
    }
}

/// System state: a compact array laid out in the module's VARIABLE declaration order
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct State {
    pub vars: Box<[Value]>,
}

impl State {
    pub fn fingerprint(&self) -> u64 {
        let mut hasher = xxhash_rust::xxh3::Xxh3::new();
        self.vars.hash(&mut hasher);
        hasher.finish()
    }
}

```

### 5.2 `tla-eval`: The Core `Next` Successor-State Generator Pattern

In TLA+, `Next` is a relational predicate that may contain multiple conjunctions (`/\`), disjunctions (`\/`), and existential quantifiers (`\E`). In Rust, the most elegant implementation is to pass around **a collection of partially bound next states (`Vec<PartialNextState>`)**:

```rust
// crates/tla-eval/src/action.rs
use tla_ast::Expr;
use tla_value::{State, Value};
use crate::error::TlaError;

/// Partially bound next state: Some(val) means the corresponding x' has been assigned; None means not yet assigned
#[derive(Clone)]
pub struct PartialNextState {
    pub slots: Vec<Option<Value>>,
    pub env: im::HashMap<tla_intern::Spur, Value>, // Variables bound locally by LET or \E
}

pub struct ActionEvaluator<'a> {
    pub curr: &'a State,
}

impl<'a> ActionEvaluator<'a> {
    /// Given an action expression and the current partial state, return every successor
    /// partial-state branch that satisfies the action
    pub fn eval_action(
        &self,
        expr: &Expr,
        state: PartialNextState,
    ) -> Result<Vec<PartialNextState>, TlaError> {
        match expr {
            // 1. Conjunction (A /\ B): pipeline (FlatMap)
            // First filter/extend the state with A, then feed each resulting new state into B
            Expr::And(lhs, rhs) => {
                let mid_states = self.eval_action(lhs, state)?;
                let mut out = Vec::new();
                for s in mid_states {
                    out.extend(self.eval_action(rhs, s)?);
                }
                Ok(out)
            }

            // 2. Disjunction (A \/ B): merge parallel branches
            Expr::Or(lhs, rhs) => {
                let mut out = self.eval_action(lhs, state.clone())?;
                out.extend(self.eval_action(rhs, state)?);
                Ok(out)
            }

            // 3. Primed-variable assignment or comparison (x' = rhs)
            Expr::Eq(lhs, rhs) if lhs.is_primed_var() => {
                let var_idx = lhs.as_primed_var_index();
                let val = self.eval_pure_expr(rhs, &state)?;
                let mut next = state;
                match &next.slots[var_idx] {
                    None => {
                        // Not yet bound: perform the assignment!
                        next.slots[var_idx] = Some(val);
                        Ok(vec![next])
                    }
                    Some(existing) if existing == &val => Ok(vec![next]), // Already bound and equal: let it through
                    Some(_) => Ok(vec![]), // Already bound but not equal: prune (this branch is FALSE)
                }
            }

            // 4. Primed-variable nondeterministic choice (x' \in S)
            Expr::In(lhs, set_expr) if lhs.is_primed_var() => {
                let var_idx = lhs.as_primed_var_index();
                let set_val = self.eval_pure_expr(set_expr, &state)?;
                let mut out = Vec::new();
                for elem in set_val.iter_elements()? {
                    let mut branch = state.clone();
                    match &branch.slots[var_idx] {
                        None => {
                            branch.slots[var_idx] = Some(elem);
                            out.push(branch);
                        }
                        Some(existing) if existing == &elem => out.push(branch),
                        Some(_) => {}
                    }
                }
                Ok(out)
            }

            // 5. UNCHANGED <<x, y>>: copy the old values from curr directly into the corresponding x', y'
            Expr::Unchanged(var_indices) => {
                let mut next = state;
                for &idx in var_indices {
                    let old_val = self.curr.vars[idx].clone();
                    match &next.slots[idx] {
                        None => next.slots[idx] = Some(old_val),
                        Some(v) if v != &old_val => return Ok(vec![]),
                        Some(_) => {}
                    }
                }
                Ok(vec![next])
            }

            // 6. Ordinary boolean guard expression (e.g. x < 3)
            _ => {
                let cond = self.eval_pure_expr(expr, &state)?;
                if cond == Value::Bool(true) {
                    Ok(vec![state])
                } else {
                    Ok(vec![]) // Condition not satisfied: prune this branch
                }
            }
        }
    }
}

```

---

## 6. Quality Assurance and Automated Conformance Testing Workflow

To make sure no operator drifts from the original TLC once written, set up the following testing workflow on day one of the project:

1. **Clone both reference repositories into sibling directories**:
   ```bash
   git clone https://github.com/aidenybai/tla-ts.git ../tla-ts
   git clone https://github.com/tlaplus/tlaplus.git ../tlaplus
   ```
2. **Pull `tla-ts`'s 542 golden snapshots**:
   In `../tla-ts`, run `pnpm install && pnpm --filter tla-ts conformance:fetch`, then symlink the generated test models and expected-result JSON into `tla-rs/tests/conformance/corpus`.
3. **Daily development loop (TDD Loop)**:
   * Pick a failing model (e.g. `TwoPhase.tla`).
   * If it reports `Unsupported operator`, search `../tla-ts/packages/tla-ts/src` for that operator's TS implementation and implement it in Rust in `tla-eval`.
   * If the resulting `Distinct states` count is wrong, enable state-log output in single-threaded mode and `diff` it against the state set from `npx tla-ts Spec.tla` to pinpoint which expression or set normalization diverged.
