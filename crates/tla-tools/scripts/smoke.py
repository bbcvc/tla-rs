#!/usr/bin/env python3
"""Runs tla-rs on a sample of the conformance corpus and checks its exit status against TLC's
recorded verdict in expected.json, as TLC's exit statuses map them.

    cargo build --release -p tla-tools
    crates/tla-tools/scripts/smoke.py ../tla-ts/packages/tla-ts/tests/conformance [--per-status 8]
        [--timeout 60] [--tla-ts ../tla-ts/packages/tla-ts]

It takes the models TLC was quickest on for each status, and runs each in its configuration's
directory with TLC's -seed 4 and -nowarning, as tla-ts recorded them. With --tla-ts it also
runs tla-ts's TLC command line on each and reports where the exit statuses differ.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

# TLC's exit status for each verdict; an error is any of TLC's error statuses.
EXPECTED_CODES = {
    "success": {0},
    "assumption-violation": {10},
    "postcondition-violation": {10},
    "deadlock": {11},
    "invariant-violation": {12},
    "property-violation": {12},
    "liveness-violation": {13},
    "error": {75, 76, 77, 150, 151, 255},
}

# A model TLC stopped on with an error after this long ran out of resources: no verdict.
TLC_TIME_LIMIT_MS = 20_000


def run(command, cwd, timeout):
    try:
        done = subprocess.run(command, cwd=cwd, capture_output=True, timeout=timeout)
        return done.returncode
    except subprocess.TimeoutExpired:
        return None


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("conformance", type=Path, help="tla-ts's tests/conformance directory")
    parser.add_argument("--per-status", type=int, default=8)
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument("--binary", type=Path, default=None, help="the tla-rs binary")
    parser.add_argument("--tla-ts", type=Path, default=None, help="tla-ts's package directory")
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[3]
    binary = (args.binary or root / "target/release/tla-rs").resolve()
    corpora = (args.conformance / ".corpora").resolve()
    libraries = [corpora / "tlapm/library", corpora / "community/modules"]
    records = json.loads((args.conformance / "expected.json").read_text())

    sample = []
    for status in EXPECTED_CODES:
        models = [
            record
            for record in records
            if record["status"] == status
            and not (status == "error" and record.get("tlcMilliseconds", 0) > TLC_TIME_LIMIT_MS)
        ]
        models.sort(key=lambda record: record.get("tlcMilliseconds", 0))
        sample.extend(models[: args.per_status])

    failures = 0
    differences = 0
    for record in sample:
        config = corpora / record["id"]
        spec = config.with_suffix(".tla")
        command = [str(binary), spec.name, "-config", config.name, "-seed", "4", "-nowarning"]
        for library in libraries:
            command += ["-library", str(library)]
        code = run(command, config.parent, args.timeout)
        expected = EXPECTED_CODES[record["status"]]
        verdict = "ok" if code in expected else "FAIL"
        failures += verdict == "FAIL"
        line = f"{verdict:4} {record['status']:24} exit {code}  {record['id']}"
        if args.tla_ts:
            cli = str((args.tla_ts / "src/cli.ts").resolve())
            library = ":".join(str(directory) for directory in libraries)
            oracle = ["bun", cli, f"-DTLA-Library={library}", "tlc2.TLC", spec.name]
            oracle += ["-config", config.name, "-seed", "4", "-nowarning", "-noGenerateSpecTE"]
            oracle_code = run(oracle, config.parent, args.timeout)
            if oracle_code != code:
                differences += 1
                line += f"  (tla-ts exits {oracle_code})"
        print(line, flush=True)

    summary = f"{len(sample) - failures}/{len(sample)} exit statuses agree with expected.json"
    if args.tla_ts:
        summary += f", {differences} differ from tla-ts"
    print(summary)
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
