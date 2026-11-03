# Evaluation of the tla-rs Plan

Assessment of [DESIGN.md](DESIGN.md) against the reference implementations, written on 2026-11-03 before any code. The plan is feasible, but it is larger than it states, and several of its design points would produce state counts that differ from TLC. Where this document conflicts with DESIGN.md, this document wins.

## What was checked

**tla-ts** (`aidenybai/tla-ts`, MIT, v0.0.6) is about 134k lines of TypeScript, most of it in the prover. The model-checking core (`parser`, `resolve`, `evaluate`, `values`, `successors`, `check`, `environment`, `instances`, `search`) is about 15k lines. Level checking, liveness, the tableau, symmetry, and a TLC-emulation layer (`src/tlc/`) add several thousand more.

**The conformance suite** lives in `packages/tla-ts/tests/conformance/expected.json`: 823 recorded TLC results from 16 corpora pinned by commit in `corpora.json` (TLC's `test-model` 402, Spectacle 169, tlaplus/Examples 106, fabracht/tla-rs 48, and others). The repository does not ship a list of 542 models. That number is a row in the tla-ts README benchmark table. 733 of the 823 models have TLC runs of 20 s or less, which is the runner's default cut-off.

| Recorded status | Models |
| --- | ---: |
| success | 482 |
| error | 156 |
| liveness-violation | 64 |
| deadlock | 63 |
| invariant-violation | 40 |
| assumption-violation | 16 |
| property-violation | 2 |

The comparison is stricter than DESIGN.md says. `compareOutcome` in `scripts/conformance.ts` checks the status, the violated property's name, `generatedStates`, `distinctStates`, `depth`, and `traceLength`.

**Prior art in Rust:**

| Project | License | Notes |
| --- | --- | --- |
| `fabracht/tla-rs` | MIT / Apache-2.0 | Published as `tla-checker`. Targets "a supported subset". Same name as this project. |
| `ddalton/tla-mc` | MIT | Compiles a spec into a native checker rather than interpreting it. |
| `zoratu/tlaplusplus` | GPL-3.0 | License rules out reuse. |

None of them targets full TLC conformance with an interpreter, so starting fresh as the plan says still stands. The name collides with `fabracht/tla-rs` if this project is ever published.

**tree-sitter-tlaplus** 1.5.0 (MIT) builds against `tree-sitter` 0.27 through `tree-sitter-language`. It parses all of TLA+, including proofs and PlusCal, with error recovery.

**Environment:** Java isn't installed on the development machine, so TLC can't run locally as an oracle yet. `expected.json` covers the corpus in the meantime.

## Design revisions

**R1. Value ordering can't be derived.** TLC orders strings and model values by when it first interned their text: configuration values first, then TLC's startup strings, then each module's tokens in the order SANY parses them. It orders sets by size and then element by element, functions by domain size and then keys and values, and intervals by size and then lower bound. `CHOOSE` returns the first element in this order, so a derived `Ord` changes what `CHOOSE` returns and therefore the state count. `Value` gets a hand-written comparison ported from `compareValues` in `values.ts`, and the string order is ported from `getTlcStringOrder` in `tlc/order.ts`. Comparing values of different kinds is an error in TLC, not an ordering.

**R2. Integers are 32-bit.** TLC's integers are Java `int`s (tla-ts: `MAXIMUM_INTEGER = 2147483647`), and overflow is an error. `Value` stores small integers with TLC's overflow checks and drops `num-bigint`. This is also a large speed win.

**R3. Equality and hashing must be semantic.** `1..3 = {1, 2, 3}` is `TRUE`, and so is equality between any lazy set and its explicit form. A derived `PartialEq` and `Hash` over an enum that mixes lazy and explicit forms gets this wrong. Values stored in a state are normalized (lazy sets are enumerated, as TLC does when it fingerprints them), and comparisons between lazy and explicit forms go through a semantic equality. Fingerprints only need to agree with that equality. They don't need to reproduce TLC's FP64 bits.

**R4. Successor generation uses continuations.** The `Vec<PartialNextState>` sketch materializes every branch and clones the environment for each one. It also has no case for `\E` and treats non-Boolean guards as `FALSE`. The evaluator instead passes a continuation and assigns primed slots in place with undo, which is the shape of TLC's `getNextStates`. Non-Boolean guards and incompletely specified successors are errors, as in TLC.

**R5. Liveness is part of done.** 66 recorded results are liveness or property violations, and successful runs of specs with `PROPERTY` need the checker too. Liveness becomes its own phase instead of an optional extra.

**R6. Syntax errors need SANY's strictness.** tree-sitter recovers from errors and accepts some modules that SANY rejects. Any `ERROR` or `MISSING` node is a syntax error. SANY's level checking (tla-ts `levels.ts`) is ported later for the `error` cases.

**R7. Effort is 2–3× the plan.** The plan estimates about 11.5k lines over about 9 weeks. The code it ports is about 15k lines of TypeScript for the core, plus level checking, liveness, and the TLC-emulation layer. Expect 25–35k lines of Rust, and roughly two to three times the planned schedule to reach full conformance.

**R8. Performance targets are stretch goals.** tla-ts measures 1.1–2.4× faster than TLC. A Rust interpreter with 32-bit integers and interned strings can plausibly beat tla-ts by several times on one thread, but 10–20× TLC is unproven. Measure it after conformance, not before.

**R9. WebAssembly needs a C sysroot.** tree-sitter is written in C. A spike building `tla-parser` for `wasm32-unknown-unknown` fails in the grammar's build script: `src/tree_sitter/parser.h` includes `<stdlib.h>`, which the system clang has no headers for when it targets WebAssembly. The WebAssembly build needs wasi-sdk (or another sysroot) in CI, or a `wasm32-wasip1` target. Decide before the CLI work in step 6.

## Revised order of work

1. **Frontend**: workspace, interner, AST, tree-sitter lowering, `.cfg` parser, and a parse smoke test over real specs.
2. **Resolution**: modules, `EXTENDS`, `INSTANCE`, `LET`, operator parameters, variable slots, and level checking.
3. **Values and evaluation**: TLC ordering and string-order emulation, the expression evaluator, and the standard modules.
4. **Model checking**: continuation-based successors, the BFS checker, and a conformance runner over `expected.json`.
5. **Liveness**: tableau, product graph, and SCC search.
6. **Scale**: parallel workers, the CLI, and benchmarks against TLC and tla-ts.

## Frontend results

`crates/tla-parser/examples/parse_corpus.rs` parses every `.tla` and `.cfg` file in the 16 conformance corpora (2,052 modules and 1,108 configurations). 1,996 modules and 1,103 configurations parse. Matched against `expected.json` by path, 17 of the failures are the root module or configuration of a recorded model. 10 of those are models TLC also rejects. The other 7 use a feature the frontend doesn't lower yet:

| Model | TLC result | Cause |
| --- | --- | --- |
| `examples/.../Paxos/MCPaxos` | success | positional selector `Inv!2` |
| `examples/.../Paxos/MCVoting` | success | positional selector `Init!1` |
| `examples/.../ewd998/EWD998ChanTrace` | assumption-violation | selector `QuorumNonEmpty!:` |
| `tlc/.../suite/test206` | success | labels in subexpression selectors |
| `tlc/.../suite/test209` | success | positional selector `F(2)!3!1` |
| `tlc/.../suite/test216` | success | subexpression selector |
| `tlc/.../suite/test219` | success | selectors such as `COp(1, 2)!(3)!1!>>` |

Subexpression selectors navigate the syntax tree of a definition, so they belong with resolution in step 2, where tla-ts implements them in `src/sany/selectors.ts`. The AST will need to keep labels and selector paths instead of dropping them.

Two SANY behaviors the grammar doesn't share are handled before lowering. SANY measures a tab as reaching the next multiple of 8 columns, while tree-sitter counts it as one column, so the parser expands tabs and maps spans back to the original text. SANY skips comments, while the grammar parses PlusCal inside them, so errors inside a block comment are ignored.
