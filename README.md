<h1 align="center">tla-rs</h1>

<p align="center">
  <b>A fast TLA+ model checker in Rust that gives the same answers as TLC, state for state.</b>
</p>

<p align="center">
  <a href="LICENSE"><img alt="License" src="https://img.shields.io/badge/license-MIT-blue"></a>
  <img alt="Rust" src="https://img.shields.io/badge/rust-1.85%2B-orange">
  <img alt="Conformance" src="https://img.shields.io/badge/TLC%20conformance-766%2F772%20match%2C%200%20mismatch-brightgreen">
</p>

<p align="center">
  English | <a href="README.zh-CN.md">简体中文</a>
</p>

---

```console
$ tla-rs MCLamportMutex.tla -workers 4
Running breadth-first search Model-Checking with fp 0 and seed 0 with 4 workers on 11 cores ...
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2026-11-05 14:35:25.
Model checking completed. No error has been found.
2729079 states generated, 724274 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 61.
Finished in 04s at (2026-11-05 14:35:30)
```

## Highlights

- 🎯 **TLC's answers, exactly.** tla-rs gives the same verdict, violation name, states generated, distinct states, depth and trace length as TLC. It was checked against 823 recorded TLC runs: no model disagrees, and every model with a TLC verdict matches unless it hits the time limit.
- ⚡ **No JVM, fast from the first state.** A small spec is checked in a few milliseconds; TLC's median time on the 823 recorded models is about a second, most of it JVM startup. Large models are 2 to 3× faster than TLC on one worker.
- 🧵 **Parallel and deterministic.** `-workers N` gives the same counts as one worker, on every run. That holds even when `SYMMETRY` or `VIEW` makes which state is kept matter.
- 🔁 **A drop-in TLC command line.** tla-rs takes TLC's options and configuration files, prints TLC's messages and counterexample traces, and returns TLC's exit codes. Existing scripts and CI jobs keep working.
- 🧩 **The full language, not a subset.** It covers `INSTANCE`, recursion, `ENABLED`, `CHOOSE`, liveness and fairness, `SYMMETRY`, `VIEW` and constraints. It includes the standard modules and the Java-backed operators of TLC, TLCExt and CommunityModules.
- 🪶 **Small and self-contained.** tla-rs is one 8 MB binary. A state costs about 30 bytes besides the queue, and states are told apart by 128-bit fingerprints, twice the width of TLC's.

## Performance

The TLC times below are TLC's own times recorded with `-workers 1`. tla-rs was timed on a local machine, not the one TLC ran on, with a 60 s limit per model.

| Model size (TLC time) | Models | Median speedup, 1 worker |
| --- | ---: | ---: |
| < 2 s | 624 | 73× |
| 2 – 10 s | 91 | 17× |
| 10 – 60 s | 33 | 3.1× |
| > 60 s | 9 | 2.8× |

Speedups on small models come mostly from not starting a JVM. Speedups on large models come from the checker itself.

Some large models:

| Model | Distinct states | TLC | tla-rs, 1 worker | tla-rs, 4 workers |
| --- | ---: | ---: | ---: | ---: |
| Detlefs | 952,912 | 82.3 s | 31.7 s | **9.4 s** |
| Crossword_MC | 485,988 | 120.1 s | 50.8 s | **16.8 s** |
| TLCSailfish1 | 109,604 | 77.2 s | 32.2 s | **10.0 s** |
| MCLamportMutex | 724,274 | 33.1 s | 14.4 s | **4.7 s** |
| MCbtree | 374,727 | 40.2 s | 20.7 s | **6.7 s** |
| GameOfLife | 65,536 | 63.6 s | 12.9 s | **4.1 s** |

Across all 757 models that match on one worker, tla-rs is faster on 750. It takes 670 s in total, against TLC's 2,441 s.

## How it compares

| | TLC | tla-rs |
| --- | :---: | :---: |
| State counts | reference | identical on 766 / 772 models, 0 mismatches |
| Runtime | JVM | native binary, no runtime |
| Liveness and fairness | ✅ | ✅ |
| Parallel search | ✅ | ✅, counts identical to one worker |
| Command line, messages, exit codes | ✅ | ✅ TLC-compatible |
| Fingerprint width | 64-bit | 128-bit |

Other Rust TLA+ checkers either target a subset of the language (`fabracht/tla-rs`) or compile a spec into a dedicated checker (`ddalton/tla-mc`). tla-rs interprets the full language and aims for conformance with TLC.

## Installation

| Channel | Package | Status |
| --- | --- | --- |
| crates.io | [`tla-tools`](https://crates.io/crates/tla-tools) | planned: `cargo install tla-tools` |
| npm | [`tla-rs`](https://www.npmjs.com/package/tla-rs) | planned: `npx tla-rs Spec.tla`, with prebuilt binaries |

Both install the same `tla-rs` command. Until the first release, build from source. This needs Rust 1.85 or newer:

```shell
git clone https://github.com/bbcvc/tla-rs.git && cd tla-rs
cargo build --release -p tla-tools
# the binary is target/release/tla-rs
```

## Usage

```shell
tla-rs Spec.tla                          # check Spec.tla with Spec.cfg
tla-rs Spec.tla -config Other.cfg        # use another model configuration
tla-rs Spec.tla -workers auto            # one worker per core
tla-rs Spec.tla -deadlock                # don't check for deadlock
tla-rs Spec.tla -library path/to/CommunityModules
```

Exit codes follow TLC:

| Code | Meaning |
| ---: | --- |
| `0` | no error |
| `10` | an assumption is false |
| `11` | deadlock |
| `12` | an invariant or safety property is violated |
| `13` | a liveness property is violated |
| `75` | evaluation failed |
| `150` | parse error |

See [crates/tla-tools/README.md](crates/tla-tools/README.md) for every option and exit code.

## Architecture

```
source ─► tla-tools-parser ─► tla-tools-resolve ─► tla-tools-eval ─► tla-tools-checker ─► tla-tools
                                                          ▲
                                                   tla-tools-value
```

| Crate | Role |
| --- | --- |
| `tla-tools-intern` | Process-wide interner with TLC's string order |
| `tla-tools-ast` | Syntax tree for TLA+ modules |
| `tla-tools-parser` | TLA+ modules (via tree-sitter-tlaplus) and TLC configuration files |
| `tla-tools-resolve` | Name resolution, `INSTANCE`, level checking |
| `tla-tools-value` | Values with TLC's equality, ordering, printing and fingerprints |
| `tla-tools-eval` | Expressions, initial and next states, `ENABLED`, standard modules |
| `tla-tools-checker` | Spec processing, BFS (single and parallel), liveness, symmetry |
| `tla-tools` | The `tla-rs` binary (the crate published to crates.io) |

Matching TLC state for state takes more than a correct evaluator. tla-rs reproduces TLC's ordering of strings and values, which decides what `CHOOSE` returns. It also reproduces TLC's order of variables, the way TLC enumerates successors, its 32-bit integer overflow, and the order in which its liveness checker explores the behavior graph. [EVALUATION.md](EVALUATION.md) records each of these choices.

## Testing

```shell
cargo test --workspace

# the full conformance suite (needs the tla-ts repository next to this one)
C=../tla-ts/packages/tla-ts/tests/conformance
cargo run --release -p tla-tools-checker --example conformance -- $C/.corpora \
  --library $C/.corpora/tlapm/library --library $C/.corpora/community/modules \
  --expected $C/expected.json --timeout 60 --jobs 4 [--workers 4] [--filter NAME]
```

The conformance runner checks each model in its own process and compares the result with TLC's recorded outcome. The 823 models come from 16 corpora, including TLC's own test models, tlaplus/Examples, Spectacle, CCF, MongoDB and CockroachDB.

## Roadmap

**Done**

- [x] Parser, name resolution and level checking
- [x] Values with TLC's ordering, equality and fingerprints
- [x] Evaluator, initial and next states, `ENABLED`, standard modules and Java-backed operators
- [x] Safety checking: invariants, action properties, deadlock, constraints, `VIEW`, `SYMMETRY`
- [x] Liveness checking with fairness, as TLC's `-lncheck final`
- [x] Parallel breadth-first search with deterministic counts
- [x] TLC-compatible command line

**Next**

- [ ] Show the output of `Print` and `PrintT`
- [ ] Support `ALIAS` in counterexample traces
- [ ] Print SANY's parse messages and warnings exactly, and TLC's stack of nested expressions in evaluation errors
- [ ] Cut per-call evaluation overhead; about ten large models (VR_*, S2C, MoveRange) are still around 2× slower than TLC
- [ ] Bring the 15 models that time out at 60 s on one worker under the limit
- [ ] Parallel liveness checking (temporal properties run on one worker today)
- [ ] Parallel search for counterexamples (today a violation falls back to one worker for TLC's shortest trace)
- [ ] Persistent worker threads and a lock-free fingerprint set
- [ ] Disk-backed state queue and fingerprint set for state spaces larger than memory
- [ ] Simulation mode (`-simulate`), `-lncheck` during the search, `-dump`, `-continue`
- [ ] Publish `tla-tools` to crates.io and `tla-rs` to npm with prebuilt binaries, and set up CI

## Documents

- [DESIGN.md](DESIGN.md): the original design
- [EVALUATION.md](EVALUATION.md): the revisions needed to match TLC, and results for each phase
- [crates/tla-tools/README.md](crates/tla-tools/README.md): command-line options, output, and remaining differences from TLC

## Acknowledgements

- [TLC](https://github.com/tlaplus/tlaplus) is the reference that tla-rs follows.
- [tla-ts](https://github.com/aidenybai/tla-ts) provided the conformance suite and the ports of TLC's algorithms that tla-rs builds on.
- [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus) is the parser.

## License

[MIT](LICENSE)
