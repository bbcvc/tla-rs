# tla-rs

English | [简体中文](README.zh-CN.md)

A TLA+ model checker in Rust that gives the same answers as TLC.

The `tla-rs` command line takes TLC's options, prints TLC's messages, and exits with TLC's exit status. Its target is conformance with TLC, not a subset of TLA+. Conformance means the same verdict, violation name, states generated, distinct states, depth and trace length on the models that TLC checks. It is checked against 823 recorded TLC runs.

## Status

Results on the 823 models recorded by the [tla-ts](https://github.com/aidenybai/tla-ts) conformance suite, from 16 corpora: TLC's own test models, tlaplus/Examples, Spectacle, CCF, MongoDB, CockroachDB and others. Each model has a 60 s limit.

| Run | Match TLC | Mismatch | No TLC verdict | Timeout |
| --- | ---: | ---: | ---: | ---: |
| 1 worker | 757 | 0 | 51 | 15 |
| 4 workers | 766 | 0 | 51 | 6 |

- **No TLC verdict:** TLC itself failed on these 51 models after more than 20 s, so there is nothing to compare against.
- **Timeouts:** all are models TLC also needs more than 60 s for.
- **Speed:** with 1 worker, 750 of the 757 matching models finish faster than TLC. They take 670 s in total, against 2,441 s for TLC.

Supported:

- Safety checking: invariants, action properties, deadlock, `ASSUME`, `CONSTRAINT`, `ACTION_CONSTRAINT`, `VIEW` and `SYMMETRY`.
- Liveness: fairness and temporal properties, checked as `-lncheck final` does.
- `INSTANCE`, recursion, `ENABLED`.
- The standard modules, plus Java overrides of the TLC, TLCExt and CommunityModules operators.
- Parallel breadth-first search (`-workers N`). It reports the same counts as one worker.

## Quick start

Requires Rust 1.85 or newer.

```shell
cargo build --release -p tla-cli
target/release/tla-rs Spec.tla                       # checks Spec.tla with Spec.cfg
target/release/tla-rs Spec.tla -config Other.cfg -workers 4
target/release/tla-rs Spec.tla -library path/to/CommunityModules
```

Exit statuses follow TLC: `0` means no error, `11` a deadlock, `12` an invariant violation, `13` a liveness violation, and so on. See [crates/tla-cli/README.md](crates/tla-cli/README.md) for the full options and exit codes.

## Workspace

| Crate | Role |
| --- | --- |
| `tla-intern` | Process-wide interner for identifiers and strings, with TLC's string order |
| `tla-ast` | Syntax tree for TLA+ modules |
| `tla-parser` | Parses TLA+ modules (tree-sitter-tlaplus) and TLC configuration files |
| `tla-resolve` | Name resolution, `INSTANCE`, level checking |
| `tla-value` | Values with TLC's equality, ordering, printing and fingerprints |
| `tla-eval` | Evaluator: expressions, initial and next states, `ENABLED`, standard modules |
| `tla-checker` | Spec processing, BFS (single and parallel), liveness, symmetry |
| `tla-cli` | The `tla-rs` binary |

Data flows down the pipeline:

```
source ─► tla-parser ─► tla-resolve ─► tla-eval ─► tla-checker ─► tla-cli
                                         ▲
                                     tla-value
```

## Conformance tests

```shell
cargo test --workspace

C=../tla-ts/packages/tla-ts/tests/conformance
cargo run --release -p tla-checker --example conformance -- $C/.corpora \
  --library $C/.corpora/tlapm/library --library $C/.corpora/community/modules \
  --expected $C/expected.json --timeout 60 --jobs 4 [--workers 4] [--filter NAME]
```

The runner checks each model in its own process and compares the result with TLC's recorded outcome. Pass `--outcomes FILE` to write one line per model.

## Documents

- [DESIGN.md](DESIGN.md): the original design.
- [EVALUATION.md](EVALUATION.md): the design revisions it needed to match TLC, and results for each phase.
- [crates/tla-cli/README.md](crates/tla-cli/README.md): command-line options, output, and what still differs from TLC.

## Known gaps

- Output printed by `Print` and `PrintT` isn't shown.
- SANY's parse messages are approximate.
- `ALIAS` isn't supported.
- About ten large models are still around 2× slower than TLC because of per-call evaluation overhead.

## License

MIT OR Apache-2.0.
