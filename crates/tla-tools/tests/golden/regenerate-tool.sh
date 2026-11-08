#!/bin/bash
# Records the expected output of each spec here under -tool from TLC itself, which tla-ts's TLC
# command line can't produce:
#
#   TLA2TOOLS=path/to/tla2tools.jar crates/tla-tools/tests/golden/regenerate-tool.sh
#
# The expected files were recorded with TLC 1.8.0 (the Clarke release). Each Name.tool.out
# holds the exit status on its first line, then the output with the lines that name the
# program, the machine, or SANY's files left out, and times, dates, and rates replaced, as
# tests/golden.rs normalizes tla-rs's output.
set -euo pipefail
cd "$(dirname "$0")"
jar="${TLA2TOOLS:?set TLA2TOOLS to the path of tla2tools.jar}"
metadir=$(mktemp -d)
trap 'rm -rf "$metadir"' EXIT
for spec in *.tla; do
  name="${spec%.tla}"
  set +e
  # The parallel collector keeps TLC from warning that it runs without it.
  output=$(java -XX:+UseParallelGC -cp "$jar" tlc2.TLC -tool -workers 1 -seed 4 \
    -metadir "$metadir/$name" "$spec" 2>&1)
  status=$?
  set -e
  {
    echo "exit $status"
    printf '%s\n' "$output" |
      grep -v -E '^(TLC2 Version|Running breadth-first|Parsing file|Semantic processing|Linting of module)' |
      sed -E 's/[0-9]{4}-[0-9]{2}-[0-9]{2} [0-9]{2}:[0-9]{2}:[0-9]{2}/DATE/g; s/ in [0-9dhmins ]+ at / in TIME at /; s/\([0-9,]+ (d?s)\/min\)/(RATE \1\/min)/g'
  } > "$name.tool.out"
done
