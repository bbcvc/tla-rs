#!/bin/bash
# Records the expected output of each spec here from tla-ts's TLC command line, the oracle the
# golden tests compare tla-rs with:
#
#   TLA_TS=../tla-ts/packages/tla-ts crates/tla-cli/tests/golden/regenerate.sh
#
# Each Name.out holds the exit status on its first line, then the output with the lines that
# name the program, the machine, or SANY's files left out, and times and dates replaced, as
# tests/golden.rs normalizes tla-rs's output.
set -euo pipefail
cd "$(dirname "$0")"
cli="${TLA_TS:?set TLA_TS to the tla-ts package directory}/src/cli.ts"
for spec in *.tla; do
  name="${spec%.tla}"
  set +e
  output=$(bun "$cli" tlc2.TLC "$spec" -noGenerateSpecTE -seed 4 2>&1)
  status=$?
  set -e
  {
    echo "exit $status"
    printf '%s\n' "$output" |
      grep -v -E '^(TLC2 Version|Running breadth-first|Parsing file|Semantic processing|Linting of module)' |
      sed -E 's/[0-9]{4}-[0-9]{2}-[0-9]{2} [0-9]{2}:[0-9]{2}:[0-9]{2}/DATE/g; s/ in [0-9dhmins ]+ at / in TIME at /'
  } > "$name.out"
done
