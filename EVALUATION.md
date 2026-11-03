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

**R1. Value ordering can't be derived.** TLC orders strings and model values by when it first interned their text: configuration values first, then TLC's startup strings, then each module's tokens in the order SANY parses them. It orders sets by size and then element by element, functions by domain size and then keys and values, and intervals by size and then lower bound. `CHOOSE` returns the first element in this order, so a derived `Ord` changes what `CHOOSE` returns and therefore the state count. `Value` gets a hand-written comparison ported from `compareValues` in `values.ts`. Comparing values of different kinds is an error in TLC, not an ordering.

The string order is ported from `getTlcStringOrder` in `tlc/order.ts`. `tla_resolve::tlc_string_order` lists the texts TLC interns before it checks a spec, from the source text with a port of tla-ts's lexer. It agrees with tla-ts on all 920 models of the corpus. `set_order` publishes them once per spec as a table of sort keys indexed by intern number, which `Symbol::cmp` reads. Other symbols follow in this process's intern order, as strings TLC creates at runtime follow its startup strings. Comparing two strings costs one more table lookup: sorting 200,000 strings takes 9.2 ms instead of 7.6 ms, and 200,000 records 86 ms instead of 81 ms. The order is process-wide, so a process checks one spec at a time, and sets the order before it builds the spec's values.

**R2. Integers are 32-bit.** TLC's integers are Java `int`s (tla-ts: `MAXIMUM_INTEGER = 2147483647`), and overflow is an error. `Value` stores small integers with TLC's overflow checks and drops `num-bigint`. This is also a large speed win.

**R3. Equality and hashing must be semantic.** `1..3 = {1, 2, 3}` is `TRUE`, and so is equality between any lazy set and its explicit form. A derived `PartialEq` and `Hash` over an enum that mixes lazy and explicit forms gets this wrong. Values stored in a state are normalized (lazy sets are enumerated, as TLC does when it fingerprints them), and comparisons between lazy and explicit forms go through a semantic equality. Fingerprints only need to agree with that equality. They don't need to reproduce TLC's FP64 bits.

Normalization still shows in what TLC prints, so `tla-value` tracks it where it does:

- A record, or a function with string keys that `@@` builds, keeps the order the spec writes its fields in until TLC normalizes it, which TLC does to compare or fingerprint it. `ToString`, `Assert`, and error messages print that order. `Print` and `PrintT` normalize the value first and print the fields sorted. The written order is a permutation stored beside the sorted keys, so equality, ordering, and fingerprints never read it, and a record written in sorted order carries none.
- A set enumeration TLC can't sort, such as `{1, "a"}`, stays as written until something needs its order. TLC sorts it to print it, so an error message that prints it fails with the comparison that sorting makes.
- `TLCEval` normalizes its argument only where TLC computes a constant once: a constant argument, outside every binder, in a module-level definition without parameters, and not in a module that an `INSTANCE` substitutes into. Elsewhere it applies its definition, `TLCEval(v) == v`.

**R4. Successor generation uses continuations.** The `Vec<PartialNextState>` sketch materializes every branch and clones the environment for each one. It also has no case for `\E` and treats non-Boolean guards as `FALSE`. The evaluator instead passes a continuation and assigns primed slots in place with undo, which is the shape of TLC's `getNextStates`. Non-Boolean guards and incompletely specified successors are errors, as in TLC.

`Evaluator::init_states` and `Evaluator::next_states` implement this, ported from tla-ts `successors.ts`. The walk carries the state being assigned as a vector of optional values, and expressions read it through a view in which an unassigned variable is undefined. What remains to walk after a conjunct is a continuation built on the stack, so `\/`, `\E`, and `x' \in S` assign a variable, run the continuation, and undo the assignment. The walk enters calls of definitions, arguments that are actions, and instances. Once every variable has a value, the conjuncts left are predicates, as in TLC, which decides how many states a later disjunction generates. `ENABLED` runs the same walk and stops at the first successor.

Three more things decide the states generated. `x' \in S` takes the elements of `S` as TLC's `Enumerator` streams them: a lazy `UNION` or `\cup` yields the elements of each set it combines, duplicates included, until TLC caches the set. TLC caches a set as the receiver of `equals`, `compareTo`, `size`, and `fingerPrint`, so tla-value marks a lazy set cached by allocation at those points, and a set kept between evaluations, such as a constant definition's value, stays cached. An argument keeps its value while the state being assigned is unchanged, as tla-ts caches a thunk. A function of actions applied in an action, as `Actions[p]`, is walked at the argument. `Evaluator::next_actions` is TLC's split of the relation into named actions, which words an incomplete successor and labels a step.

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

`crates/tla-parser/examples/parse_corpus.rs` parses every `.tla` and `.cfg` file in the 16 conformance corpora (2,052 modules and 1,108 configurations). 2,008 modules and 1,103 configurations parse, up from 1,996 modules before the AST kept labels and subexpression references and the parser read operator symbols ending them. Matched against `expected.json` by path, 8 of the failures are the root module or configuration of a recorded model, all models TLC also rejects.

tree-sitter-tlaplus 1.5.0 reads an operator symbol between `!`s, as in `COp2!lab!:!++!lab`, and at the end with arguments, as in `COp(1, 2)!(3)!++(4, 5)`, but not at the end without them, as in `OOp5(COp!@!++, 1, 2, 3, 4, 5)` or `BY DEF Cases!\oplus`. There it leaves the symbol in an `ERROR` node, or reads it as an infix operator of what follows. Neither a later release nor an upstream issue or pull request handles it. So when a parse fails, the parser replaces each operator symbol after a `!` that isn't followed by `(` or `!` with an identifier of the same length, and parses again. It keeps the new tree only if it has no errors and each identifier is the last part of a reference, and lowering reads each one back as its operator. Any other failure keeps the error of the first parse. TLC's `test206`, `test219`, and `test219a` and tlapm's `ModuleSemanticsTheorems` parse this way.

Three SANY behaviors the grammar doesn't share are handled during or before lowering. SANY measures a tab as reaching the next multiple of 8 columns, while tree-sitter counts it as one column, so the parser expands tabs and maps spans back to the original text. SANY skips comments, while the grammar parses PlusCal inside them, so errors inside a block comment are ignored. SANY gives `ENABLED`, `UNCHANGED`, `[]`, and `<>` the precedence 4-15, so an operator after their operand that binds as tightly, as in `ENABLED x'` or `[]x = y`, is a precedence conflict, which SANY rejects. The grammar applies the prefix operator to `x` alone, so the parser reports the conflict itself.

## Resolution results

`tla-resolve` turns a root module and the modules it uses into a `Spec` whose expressions refer to state variables, constants, local slots, and definitions. TLC's standard modules are bundled as TLA+ source, as TLC bundles them, and the evaluator will replace their placeholder definitions the way TLC's Java overrides do. Each `INSTANCE` substitution becomes a definition in the instance's scope, and a parameterized instance adds a frame, so instantiated definitions are closures like `LET` definitions.

`crates/tla-resolve/examples/resolve_corpus.rs` compares the result with tla-ts's records:

```shell
C=../tla-ts/packages/tla-ts/tests/conformance
L="--library $C/.corpora/tlapm/library --library $C/.corpora/community/modules"
cargo run --release -p tla-resolve --example resolve_corpus -- $C/.corpora --all $L --sany $C/sany.json
cargo run --release -p tla-resolve --example resolve_corpus -- $C/.corpora $L --expected $C/expected.json
```

The parser and resolver agree with SANY on 1,865 of the 1,873 modules SANY was recorded on. Every one of the 823 models TLC was recorded on that TLC checks resolves.

The 9 disagreements with SANY:

| Cause | Modules | Plan |
| --- | ---: | --- |
| Proof syntax (`DEF`, `HIDE`, `BY`), which TLC ignores | 4 | Out of scope until proofs matter. |
| SANY reporting a module nested in the file as defined twice when a `LET` instantiates it | 3 | A SANY quirk; emulate only if a model depends on it. |
| A decimal literal, which SANY accepts and TLC rejects when it checks the model | 1 | Already an error, at an earlier stage than TLC's. |
| `Operators_test`, a grammar difference in proof syntax | 1 | Out of scope with proofs. |

TLC also requires the root module to be named after its file. The resolver takes source text, so the caller makes that check, as the smoke tool does.

### Subexpression references

The AST keeps labels and subexpression references such as `Inv!2`, `Op(a)!lab(b)!<<`, `Op!@`, and `I!Op!:`, and resolution follows SANY's `Generator.selectorToNode` as tla-ts `subexpressions.ts` ports it. A reference resolves to a definition of its own, made beside the definition it selects from: at its depth, in the frames of its instance, and in the names of its module's elaboration. Its parameters are those of the definition, of the labels, and of the binders on the way to the selected part, and its body is the part, inside the `LET`s around it. The reference applies it to the arguments it gives, or passes it as an operator when it gives none, as in `OOp2(SOp1a!@, 2, 2)`. Labels are otherwise transparent, except that SANY's level checks don't see an action under a label as an operator application.

With them, the parser and resolver agree with SANY on 1,860 modules, up from 1,852, and the models that fail to resolve although TLC checks them go from 7 to 2. `crates/tla-eval/examples/check_assumptions.rs` agrees with TLC on the assumptions of every model that uses them except `test206` and `test219`: `MCPaxos`, `MCVoting`, `test209`, and `test216` hold, and `EWD998ChanTrace` violates one as TLC reports. Its disagreements with TLC go from 8 to 3, those two and `NormalizationAssume`. Once the parser reads an operator symbol ending a reference (see Frontend results), `test206` and `test219` resolve and their assumptions hold, as TLC reports, which leaves 1,864 modules agreeing with SANY, no model TLC checks failing to resolve, and `NormalizationAssume` the one disagreement on assumptions.

What resolution leaves out:

| SANY behavior | Why |
| --- | --- |
| A reference into a `LET` definition by its own name, as in `LET L(y) == m :: y IN L(1)!m` | Resolution keeps the syntax tree of module-level definitions only, and reports `Cannot select a subexpression of L.` A `LET` definition reached through its definition, as in `Op1(2)!(3)!2!Op1a(4)`, works. |
| Checks of labels themselves: duplicate labels, parameters that must name the bound identifiers around them, labels outside definitions | Not checked yet. |
| References into `ASSUME ... PROVE` theorems and proof steps (`<1>1!2`) | The parser drops them. |
| The nesting of an infix chain such as `a /\ b /\ c` | Positions count the operands of the flattened chain, as tla-ts does. |

### Level checking

A level pass after resolution (`crates/tla-resolve/src/levels/`) computes SANY's level of every definition, with the highest level each parameter allows, its weights, and whether it is Leibniz in each parameter, and stores them in `Spec::levels`. It reports the first level error SANY reports. It follows tla-ts `levels.ts` for the levels, `sany/levels.ts` for SANY's checks, and `substitution-levels.ts` for `INSTANCE` substitutions.

Before the pass, the parser and resolver agreed with SANY on 1,849 modules. With it they agree on 1,852: `test213`, `test215`, and `test217` now fail with the first message SANY reports for each. No module SANY accepts gets a level error, and the 7 models that fail although TLC checks them are the same 7.

SANY checks each module once by itself, and checks each `INSTANCE` against what that module allows its constants and variables. Resolution instead copies an instantiated module's definitions with the substitutions in place. So the pass reports errors only in modules elaborated by themselves, and elaborates by itself, for the pass only, any module resolution only instantiated. The levels of an instance's definitions come from their substituted bodies.

What the pass leaves out:

| SANY check | Why |
| --- | --- |
| Constraints from `THEOREM ASSUME ... PROVE`, and the checks of proofs of temporal theorems (`Non-constant CASE for temporal goal`) | The parser drops `ASSUME ... PROVE` and proofs. |
| Unnamed theorems | Resolution doesn't resolve them. |
| The levels of an instance's definitions, which SANY maps from the module's own through the substitutions, so that a constant substituted for a variable leaves the level at 1, and an argument of a parameterized instance replacing a variable of a non-constant module may be at most a state function | Levels come from the substituted bodies, which can only allow more than SANY. |
| The location of the bound variable in SANY's message for a range above action level | The resolved program keeps no span for it. |

## Evaluation results

`tla-value` implements TLC's values. Equality and ordering cross representations (`1..3 = {1, 2, 3}`) and fail where TLC fails (`1 = "a"`). Sets and function domains are sorted in TLC's order, and sets TLC keeps symbolic, such as `SUBSET S`, `[S -> T]`, `Nat` and filters over them, stay lazy. Printing and fingerprints follow TLC. `tla-eval` evaluates the resolved program:

- Definition arguments are lazy, as in TLC, so `p'` primes the argument passed for `p`.
- Recursive and `LET` functions are lazy. Applying one evaluates its body at the argument, without building the function at each step of the recursion.
- Quantifiers, `CHOOSE` and set filters take a large set of functions, records, or tuples, or a large power set, one element at a time, in TLC's order (`Value::enumeration`), so they stop at the first witness without building the rest. A power set of more than 30 elements, too large to list, is enumerated this way, as TLC enumerates it.
- Constant definitions are computed once, with TLC's startup random generator, as TLC computes them when it starts, and a lazy set keeps its elements once enumerated.
- The model configuration binds constants, overrides definitions, and defines operator tables.
- Native implementations replace the definitions TLC overrides in Java. These are Naturals, Integers, Sequences, FiniteSets, TLC, TLCExt, Bags, Json, Randomization and `_Possible`, plus IOUtils' `Serialize` for NDJSON, which TLC's own Json class writes.
- `Evaluator::with_community_modules` adds the community module IOUtils, as TLC has it when `CommunityModules-deps.jar` is on its class path. That covers `IOEnv`, `atoi`, the `IOExec` family, and plain text `Serialize` and `Deserialize`. Without the jar, TLC evaluates IOUtils' TLA+ placeholders. The commands only run once `Runtime::allow_exec` allows them. Java's object serialization (`IOSerialize`, `IODeserialize`) isn't ported and fails with an error.

`crates/tla-eval/examples/check_assumptions.rs` checks every model's `ASSUME`s, as TLC does before it explores any state, and compares the outcome with TLC's recorded status. Each model runs in a child process with a timeout. `--outcomes FILE` writes every model's outcome, so two builds can be compared model by model.

```shell
C=../tla-ts/packages/tla-ts/tests/conformance
cargo run --release -p tla-eval --example check_assumptions -- $C/.corpora \
  --library $C/.corpora/tlapm/library --library $C/.corpora/community/modules \
  --expected $C/expected.json --timeout 20
```

It checks 920 models in 22 seconds on 11 cores. Outcomes: 854 satisfied, 22 violated, 43 failing before evaluation, and 1 timing out. Each model is checked in its configuration's directory, where tla-ts's recorder ran TLC, so relative paths such as `./example.ndjson` resolve as they did for TLC.

On the first run, 51 models disagreed with TLC; none do now. The last three to agree:

- `test206` and `test219` end a subexpression reference with an operator symbol that takes no arguments. The parser now reparses them with the symbol masked (see Frontend results).
- `NormalizationAssume`: records and `@@` functions keep the order the spec writes their fields in, until TLC would normalize them; printing an unsortable set in an error message fails as in TLC; and `TLCEval` normalizes its argument only where TLC computes it once (see R3).

The recorder ran TLC with `tla2tools.jar` alone on its class path (`scripts/record-tlc.ts` in tla-ts), so the CommunityModules' Java overrides were off, and TLC evaluated IOUtils' TLA+ placeholders. Six models get their outcomes from those placeholders, in TLC and here: `EWD998ChanTrace`, `SmokeEWD998_SC`, `MCccfraft`, `Traceccfraft`, `Traceetcdraft`, and `StringDeserialize`. With `--community-modules`, the run evaluates as TLC does with `CommunityModules-deps.jar`. Then `Traceetcdraft` satisfies its assumptions where the recording reports a violation, because the `./example.ndjson` it reads exists beside it, `Traceccfraft`, `EWD998ChanTrace` and `StringDeserialize` violate theirs on files that are missing, as recorded; `MCccfraft`'s hold, and TLC's recorded error comes after them; and `SmokeEWD998_SC` stops where IOUtils would run a command. `--allow-exec` lets IOUtils run commands, which no verification run does: `SmokeEWD998_SC` forks 180 TLC processes.

The timeout is `CarTalkPuzzle` Model_3. Its `Break` filters about 2.6e10 functions, which TLC can't finish either, so TLC has no recorded result for it.

What TLC does that the run turned up:

- An assumption that fails to evaluate counts as violated.
- TLC checks neither `AXIOM`s nor the assumptions of modules the spec only instantiates. It checks the root module's and those of the modules it extends.
- The configuration ignores assignments to names the specification lacks, such as `n1 = n1` for a model value.
- `<-` may name `TRUE`, `FALSE`, `BOOLEAN`, `STRING` or another constant.
- An entry scoped with `[M]` replaces the definition in module `M` for every instance of it.
- `TLCGet("config")` answers from the configuration and the checker's options before any state is explored.
- `AssertError`, `TLCDefer` and `TLCGet` see their arguments unevaluated.
- A set of functions with an empty domain is `{<<>>}`, whatever its range.
- TLC prints a record, or a function `@@` builds with string keys, in the order its fields are written until it compares or fingerprints it, and sorted from then on.

Still missing from evaluation:

| Gap | Effect |
| --- | --- |
| `ENABLED` | Needs successor generation, which comes with the model checker. |
| Natives for the other community modules TLC overrides in Java, such as CSV, and `TLCGet("config").install` | Only matter with `--community-modules`; CSV's writers stay `TRUE`, and `SmokeEWD998_SC`'s command has no jar to run. |
| TLC's order of computing constant definitions at startup | `Evaluator::evaluate_constant_definitions` goes through the definitions in the resolver's order. TLC goes through the modules in the order SANY finishes them, through each module's definitions in the order of SANY's symbol table (tla-ts `createTlcDefinitionOrder`), and skips the modules an `INSTANCE` gives parameters to. Values are the same; impure natives in several constant definitions, such as `Print` or `RandomElement`, can run in another order. |
| Streaming the elements of a lazy set before TLC caches them | TLC enumerates a `UNION` or `\cup` it hasn't cached by streaming the sets it combines, duplicates and all (tla-ts `getStreamedElements`). This matters for how many successors TLC generates. |
| A graceful error on deep recursion | Each recursion level uses about 2.6 KB of stack in release builds. The checker should evaluate on threads with large stacks. |
| `PickSuccessor`, `TLCCache`'s caching, and `AssertError`'s check that its message is a string literal | Small; they matter only for the specs that use them. |

## Model checking results

`tla-checker` checks a model as TLC does with `-workers 1`. `check` takes a resolved spec, the model configuration, and a function that gives it the states (`Successors`). The evaluator implements `Successors` with its initial and next state generation. The tests implement it with small hand-written transition systems, so the search is tested apart from successor generation. `check` follows TLC's order:

1. Bind the configuration.
2. Process the spec.
3. Check the definitions the configuration substitutes for constants.
4. Start the runtime and compute the constant definitions.
5. Check the constant parts of the spec and configuration.
6. Build the symmetry group.
7. Check the assumptions.
8. Build the liveness checker, for a spec with temporal properties.
9. Search, adding each state to the liveness checker's behavior graphs.
10. Look for a liveness counterexample in the graphs.
11. Check the postconditions.

The modules:

- **`plan`** is TLC's `SpecProcessor`. `SPECIFICATION` splits into its initial conjuncts, one `[][Next]_v`, and temporal conjuncts. The split follows zero-arity definitions, those of parameterized instances (`I(y)!Spec`) included. `PROPERTY` splits the same way:
  - `[]P` with a state predicate `P` is checked like an invariant named after `P`;
  - `[][A]_v` is checked on every step as `A \/ UNCHANGED v`;
  - a state predicate is checked on the initial states;
  - the rest is left to liveness.

  Each part that isn't a zero-arity definition gets a synthesized one, appended to `Spec.defs` with its levels. A part inside a parameterized instance gets a module-level definition that calls into the instance's frame. Constant parts are evaluated when the checker starts. A `TRUE` one is dropped, and the rest are TLC's errors. INIT/NEXT, CONSTRAINT, ACTION_CONSTRAINT, VIEW, `_POSSIBLE`, POSTCONDITION, RL reward and periodic are looked up and rejected with TLC's messages.
- **`level`** has two notions of level, and TLC uses each where tla-ts does. TLC's level bound (`Spec.getLevelBound`, tla-ts `getLevel`) counts every argument of an operator: it sorts parts and finds constants. SANY's level counts an argument only where the operator uses its parameter: TLC checks invariants (`Ignore(x)` with an unused parameter is a constant to SANY) and the substitutes for constants by it. Both raise TLC's Java overrides that read the checker's state (`TLCGet`, `_Counts`, `RandomSubset`, ...) to state level.
- **`search`** is the breadth-first search: a set of fingerprints, a FIFO queue, and a parent link and depth per state for traces. Like TLC, it drops a state once it has expanded it, and rebuilds the behavior to a violation from the initial states by the fingerprints along it. It keeps the states only when the spec extends TLCExt, whose `Trace` reads them as the search runs. A state costs about 30 bytes besides the queue: a 128-bit fingerprint (two seeded foldhash lanes over one pass of the values), a parent index, a depth, and a slot in a hashbrown table of indices. Counting:
  - Every initial state and every successor counts as generated, repeats included.
  - An initial state that the constraints keep and that was seen already is skipped.
  - Invariants are checked on any successor that isn't a stored state, so a state the constraints exclude is still checked.
  - Implied actions are checked on every step.
  - A state with no successors is a deadlock when `CHECK_DEADLOCK` is on.

  The runtime's statistics are published as each state is found, so `TLCGet("distinct")` already counts a new state while its invariants are checked. `TLCGet("level")` is the depth of the state being checked. `TLCSet("exit", TRUE)` stops the search between expansions.
- **`fingerprint`** tells states apart by the variables or by the `VIEW`. With a `SYMMETRY`, it closes the permutations under composition and takes the smallest fingerprint over the orbit.
- **`liveness`** is TLC's liveness checking with `-lncheck final`, ported from tla-ts `liveness.ts`, `tableau.ts` and `liveness-checker.ts`:
  - Spec processing makes each temporal part of the properties and of the spec a module-level definition, and adds a definition `ENABLED <<A>>_v` beside each fairness condition. When the checker is built, it translates them as tla-ts `toLiveExpression` does, with values at hand: it expands the definitions a formula applies in the frames of their calls, recursive ones included, decides `IF`s with constant conditions, unrolls quantifiers over constant sets, and takes each part below temporal level as one formula it evaluates in its frames. tla-eval's scope API (`scope.rs`: `module_frames`, `call_frames`, `bind`, `eval_in`) keeps those frames.
  - The negated properties, conjoined with the fairness, go to disjunctive normal form. Each disjunct is sorted into conditions on a cycle (`<>[]A`, `[]<>S`, `[]<>A`) and a temporal rest, whose tableau the behavior graph is the product with.
  - The search adds each new initial state, and each expanded state with its successors in the model, to the behavior graph of each solution, with the results of the solution's checks. The successors go in the order TLC's `SetOfStates` iterates them, by TLC's fingerprint of each state over its variables in TLC's order.
  - Once the search is done, a Tarjan search finds a strongly connected component that satisfies a model, and the lasso TLC prints through it, whose length TLC reports with the stuttering step at the end of a one-state cycle.
  - It evaluates less than TLC where the outcome can't differ: a fairness condition on the spec's next-state relation holds on every step of the graph that changes its subscript, since the search found the step as a successor; and without a `VIEW` or `SYMMETRY`, the results of the state predicates are kept by the state's index in the search.
- **`postcondition`** runs after a search that finds no violation. A postcondition TLC computed at startup is an error. A `_POSSIBLE` predicate that no state or step in the model witnessed is a violation, and so is a postcondition that is false or fails. TLC exits as for a violated assumption in both cases.

`crates/tla-checker/examples/conformance/` checks every recorded model and compares it with TLC the way tla-ts's `compareOutcome` does: status, violation name, states generated, distinct states, depth, and trace length. Each model runs in a child process, because TLC's string order is the process's, on a thread with a 1 GB stack and under a timeout. `--filter` selects models and `--outcomes FILE` writes each model's outcome with the milliseconds its child process ran. The run ends with the time against TLC's recorded time on the models that match: the median ratio, how many are faster, and the slowest ratios.

```shell
C=../tla-ts/packages/tla-ts/tests/conformance
cargo run --release -p tla-checker --example conformance -- $C/.corpora \
  --library $C/.corpora/tlapm/library --library $C/.corpora/community/modules \
  --expected $C/expected.json --timeout 60 --jobs 8
```

| Run | Match | Mismatch | Unsupported | No verdict | Timeout | Crash |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| First full run | 636 | 44 | 60 | | 82 | 1 |
| Safety only | 653 | 18 | 70 | 51 | 30 | 1 |
| With liveness | 708 | 31 | 0 | 51 | 32 | 1 |
| Now | 741 | 9 | 0 | 51 | 22 | 0 |

All 823 models run in 11 minutes on 8 jobs. 741 of the 772 models with a TLC verdict match. On them the median ratio of the checker's wall time to TLC's is 0.019, and the checker is faster on 731 (TLC's times include starting the JVM).

- **No verdict (51)** are models where TLC stopped with an error after more than 20 s. That is TLC running out of memory or disk on a state space too large for it, and tla-ts's runner leaves these out too.
- **Timeouts (22)** are all models TLC took more than 20 s on. `cf1s_folklore` (TLC 271 s) spends its time evaluating its fairness action, a part of its next-state relation, on every step of the behavior graph.

Of the 70 models liveness checking decides, 66 match. TLC's liveness counterexamples depend on TLC's order of the variables, the reverse of the root module's SANY `Context` enumeration (`tla_resolve::tlc_variable_order`, which agrees with tla-ts on all 912 models both read): it decides TLC's fingerprint of a state, which orders a state's successors in the behavior graph.

The first run found these; they are fixed:

- VIEW and SYMMETRY (nine models).
- `_POSSIBLE` and POSTCONDITION.
- TLC's level bound for operator arguments (`ModuleOverwrites`), next to SANY's levels for invariants (`operator_arguments`).
- Specifications through parameterized instances (`test61`).
- Rejecting a substitute for a constant that fails without a state (`etest7`, `TLCGetNamedUndefined`).
- Publishing statistics as states are found (`EWD998Chan` stops on `TLCGet("distinct") > 500`).
- Liveness checking, which also settles `InitialLivenessEvaluationError`: TLC fails evaluating `ENABLED` on the initial state as it adds it to the behavior graph.

What is left, by cause:

| Cause | Models |
| --- | --- |
| `ENABLED` of a fairness condition of an instance whose variables are substituted by definitions, as a refinement property `TD!Spec` has: the evaluator fails on a primed substitute in the state being assigned, or answers otherwise than TLC's context quirk | `EWD840` (both), `EWD998ChanID` (both), `EWD998`, `MCParReach`, `glowingRaccoon/product`, `Github725f`, `Github725g` |
