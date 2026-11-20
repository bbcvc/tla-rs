# tla-tools

`tla-rs` checks a TLA+ spec with its model configuration the way `java tlc2.TLC` does. It
takes TLC's options, prints TLC's messages, and exits with TLC's exit status.

## Running it

```shell
cargo build --release -p tla-tools
target/release/tla-rs Spec.tla                      # checks Spec.tla with Spec.cfg
target/release/tla-rs Spec.tla -config Other.cfg -deadlock -seed 4
target/release/tla-rs Spec.tla -library path/to/CommunityModules
cargo run --release -p tla-tools -- Spec.tla          # the same, through cargo
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
| `-tool` | Frame each message with TLC's code and level, for a program that reads the output. |
| `-workers N\|auto` | Workers of the breadth-first search (`auto`: one per core). The counts are those of one worker. |
| `-fp N` | Only `0` is accepted: tla-rs fingerprints states as TLC does with `-fp 0`. |
| `-lncheck final\|default\|...` | Accepted. tla-rs checks temporal properties once the search is done, as `final` does. |
| `-metadir DIR` | Ignored: tla-rs keeps its states in memory. |
| `-noGenerateSpecTE` | Accepted. tla-rs generates no trace exploration spec. |
| `-library DIR` | A directory of modules, searched recursively. Repeatable. `-DTLA-Library=a:b` works too. |
| `-dump [dot[,colorize][,actionlabels][,snapshot]] FILE` | Write each distinct state to `FILE.dump`, or the state graph to `FILE.dot`, as TLC does. |

The options also take two dashes (`--config`). `tla-rs --help` lists them.

## Output and exit status

tla-rs prints what TLC prints: the startup banner, the files it parses, `Computing initial
states...`, the progress of a long search every minute, and at the end the verdict, the
behavior that leads to a violation (`State 1: <Initial predicate>`, `State 2: <Next line ...>`,
with `/\ var = value` in TLC's order of the variables and `Back to state N` or `Stuttering` for
a liveness counterexample), and the counts of the search. With an `ALIAS`, each state of the
behavior shows the fields of the alias's record instead of the variables, as TLC does. What a
spec prints with `Print` or `PrintT` appears where TLC prints it, including the lines it
prints as TLC computes the states of a counterexample again and evaluates their alias.

With `-tool`, each message is framed as TLC frames it for the Toolbox and other programs that
read its output, with its code from TLC's `EC` and its level (0 none, 1 error, 3 warning, 4
state):

```text
@!@!@STARTMSG 2110:1 @!@!@
Invariant Inv is violated.
@!@!@ENDMSG 2110 @!@!@
```

Under `-tool`, tla-rs also prints what TLC adds there: `Starting SANY...` and `SANY finished.`
around SANY's report, the counts of the search again as progress with the states per minute,
`N: Back to state: <Action>` as a state, and the time it ran in milliseconds. An error TLC
raises with a code is framed with that code also where it is nested in another message, such
as the cause of `Evaluating invariant Inv failed.` or the `_ALIASEvalError` of a state. What
the spec prints with `Print` and `PrintT`, and SANY's report, are printed without a frame, as
TLC prints them.

With `-dump FILE`, tla-rs lists each distinct state it finds in `FILE.dump` (`State 1:` and
the state), as TLC does. With `-dump dot FILE`, it writes the state graph to `FILE.dot` in
TLC's DOT format instead: a node for each state, named by TLC's 64-bit fingerprint of it and
labeled with the state, or its `ALIAS`; an edge for each step the search takes; and the
states of each level of the search on one rank. `actionlabels` labels each edge with its action
and the values of the action's parameters, as `Request(0)`; `colorize` colors the edges by
action and adds a legend; `snapshot` also keeps the graph so far in `FILE_snapshot.dot`. The
file has TLC's extension added unless it already ends with it. A search that dumps its states
runs on one worker, as TLC's does, and writes the same graph as TLC 1.8.0 does.

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

## SANY's XML export

`tla-rs tla2sany.xml.XMLExporter [-I DIR]... [-o] [-t] [-r] FILE` prints SANY's semantic tree
of the spec as XML on stdout, as `java tla2sany.xml.XMLExporter` does, and SANY's report on
stderr. A spec SANY rejects exits with 2 after `ERROR: Failed to parse module.`, and an
argument it can't read with 1. A Java main class as the first argument picks the tool, so
`tla-rs tlc2.TLC Spec.tla` is `tla-rs Spec.tla`.

The export follows SANY's schema as far as tools built on TLC read it. `context` has an entry
for each module, each `CONSTANT` and `VARIABLE` (`OpDeclNode`, with its `kind`: 2 for a
constant, 3 for a variable), and each definition at the top level of a module
(`UserDefinedOpKind`), with its location, SANY's level, its name and its arity. Each module
refers to what it holds, and the root module to everything it can name. The nodes are numbered
in the order SANY creates them, not with SANY's numbers, so the variables come out in SANY's
order when they are sorted by number, as the statechart skill of cursor/plugins sorts them. Of
the 769 specs of the conformance corpus that both SANY and tla-rs read, what the skill reads
is the same as in SANY's export on all of them. What the export leaves out:

- the bodies and parameters of definitions, the built-in operators, and `LET` definitions;
- the definitions SANY adds for an instance, `I!Op`, and the nodes of theorems and assumptions;
- a standard module that an `-I` directory replaces: tla-rs always uses its own.

As SANY does, the export refuses a spec with a string holding a character XML 1.0 can't
represent, and exits with 7.

## Tests

`cargo test -p tla-tools` runs the golden tests: each spec in `tests/golden` is checked, and its
output and exit status are compared with tla-ts's TLC command line, once times, dates, the
banner, and SANY's file lines are normalized. `tests/golden/regenerate.sh` records them again
from tla-ts. Each spec is also checked under `-tool` against `Name.tool.out`, which TLC 1.8.0
recorded itself, since tla-ts has no `-tool`; the rates TLC prints there are normalized too.
`TLA2TOOLS=path/to/tla2tools.jar tests/golden/regenerate-tool.sh` records them again.

`tests/dump.rs` compares `-dump` with TLC's graphs, and `tests/xml.rs` compares what the
statechart skill reads of the XML export with what it reads of SANY's, both on the runs of the
skill in `tests/statechart`.

`scripts/smoke.py` runs a sample of the conformance corpus for each status and checks the exit
status against TLC's recorded verdict, and with `--tla-ts` against tla-ts's own exit status:

```shell
C=../tla-ts/packages/tla-ts/tests/conformance
cargo build --release -p tla-tools
crates/tla-tools/scripts/smoke.py $C --per-status 8 --tla-ts ../tla-ts/packages/tla-ts
```

## Not yet like TLC

- SANY's report follows SANY's: the file it parses each module from, each module it analyzes
  and lints, and a semantic or fatal error. A standard module is reported as copied into a
  directory of its own, as TLC does, without the path of `tla2tools.jar`. Like SANY, tla-rs
  goes on after a semantic error and reports every one, after the module SANY analyzes it in,
  and prints SANY's warnings and its linter's. Some errors are still in tla-rs's own words where
  SANY words them differently, such as an operator given the wrong number of arguments, and
  tla-rs doesn't check proofs, so it reports none of SANY's errors in them. A module that only
  an `INSTANCE` with substitutions uses isn't linted. With a semantic error, tla-rs reports no level errors,
  where SANY still level-checks the modules it analyzed before it, and two errors with the same
  text at the same place are reported once. tla-rs parses with tree-sitter, so a
  syntax error is reported inside SANY's report of it, but in tree-sitter's words and at the
  position tree-sitter finds it.
- With temporal properties to check, a spec's `Print` and `PrintT` may print more or fewer
  times while the search runs than in TLC, which evaluates the actions again for the liveness
  checker. Without them, and in a counterexample, they print as in TLC.
- An error computing the initial states or the successors of a state is printed with TLC's
  stack of nested expressions, but an error in a value TLC evaluates lazily, such as a set
  filter TLC fingerprints, isn't printed with TLC's fingerprint stack trace, and an error TLC
  raises as a Java exception, such as an index out of a tuple's bounds, isn't worded as TLC's
  unexpected exception.
- The collision estimate from the actual fingerprints, which TLC adds for large state spaces,
  isn't printed.
- Under `-tool`, tla-rs finds the code of an error by the wording of TLC's template for it
  (`tla_tools_checker::message`). An error whose wording matches none of the templates there
  is printed as an error TLC raises without a code: with code 1000 at the top, and without a
  frame where it is nested.
- `-lncheck`, `-dump`, and `-continue` aren't implemented.
