# tla-cli

`tla-rs` checks a TLA+ spec with its model configuration the way `java tlc2.TLC` does. It
takes TLC's options, prints TLC's messages, and exits with TLC's exit status.

## Running it

```shell
cargo build --release -p tla-cli
target/release/tla-rs Spec.tla                      # checks Spec.tla with Spec.cfg
target/release/tla-rs Spec.tla -config Other.cfg -deadlock -seed 4
target/release/tla-rs Spec.tla -library path/to/CommunityModules
cargo run --release -p tla-cli -- Spec.tla          # the same, through cargo
```

The spec can be named `Spec.tla`, `Spec`, or `Spec.cfg`. Without `-config`, the configuration
is the spec's file with `.cfg`, as TLC does. The modules the spec uses are read from the spec's
directory, then from each library directory. A Java class beside the spec that overrides a
module's operators is loaded as TLC loads it.

| Option | Meaning |
| --- | --- |
| `-config FILE` | The model configuration. |
| `-deadlock` | Don't check for deadlock. |
| `-seed N` | The seed of TLC's random choices (default 0). |
| `-nowarning` | Don't print warnings. |
| `-workers N\|auto` | Workers of the breadth-first search (`auto`: one per core). The counts are those of one worker. |
| `-fp N` | Only `0` is accepted: tla-rs fingerprints states as TLC does with `-fp 0`. |
| `-lncheck final\|default\|...` | Accepted. tla-rs checks temporal properties once the search is done, as `final` does. |
| `-metadir DIR` | Ignored: tla-rs keeps its states in memory. |
| `-noGenerateSpecTE` | Accepted. tla-rs generates no trace exploration spec. |
| `-library DIR` | A directory of modules, searched recursively. Repeatable. `-DTLA-Library=a:b` works too. |

The options also take two dashes (`--config`). `tla-rs --help` lists them.

## Output and exit status

tla-rs prints what TLC prints: the startup banner, the files it parses, `Computing initial
states...`, the progress of a long search every minute, and at the end the verdict, the
behavior that leads to a violation (`State 1: <Initial predicate>`, `State 2: <Next line ...>`,
with `/\ var = value` in TLC's order of the variables and `Back to state N` or `Stuttering` for
a liveness counterexample), and the counts of the search.

| Exit status | Meaning |
| ---: | --- |
| 0 | No error found. |
| 10 | An assumption is false, or a postcondition fails. |
| 11 | Deadlock. |
| 12 | An invariant or a safety property is violated. |
| 13 | A liveness or action property is violated. |
| 75 | Evaluating the spec failed. |
| 76 | An invariant is not a state predicate. |
| 150 | The spec can't be parsed. |
| 151 | The configuration is wrong. |
| 255 | Another error, or a model tla-rs doesn't support yet. |
| 1 | The command line can't be read. |

## Tests

`cargo test -p tla-cli` runs the golden tests: each spec in `tests/golden` is checked, and its
output and exit status are compared with tla-ts's TLC command line, once times, dates, the
banner, and SANY's file lines are normalized. `tests/golden/regenerate.sh` records them again
from tla-ts.

`scripts/smoke.py` runs a sample of the conformance corpus for each status and checks the exit
status against TLC's recorded verdict, and with `--tla-ts` against tla-ts's own exit status:

```shell
C=../tla-ts/packages/tla-ts/tests/conformance
cargo build --release -p tla-cli
crates/tla-cli/scripts/smoke.py $C --per-status 8 --tla-ts ../tla-ts/packages/tla-ts
```

## Not yet like TLC

- SANY's messages are approximate: tla-rs prints `Parsing file` for the files it reads and
  `Semantic processing of module` for each module, but not the standard modules' paths, the
  linting lines, or SANY's warnings.
- What a spec prints with `Print` or `PrintT` isn't shown.
- An evaluation error is printed without TLC's stack of nested expressions.
- The collision estimate from the actual fingerprints, which TLC adds for large state spaces,
  isn't printed.
- `-lncheck`, `-dump`, `-tool`, and `-continue` aren't implemented.
