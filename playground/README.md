# Playground

Tools built on TLC, run on tla-rs instead.

## statechart

`statechart/` is the statechart skill of [cursor/plugins](https://github.com/cursor/plugins)
(`harness/pstack/claude-code/skills/statechart`, at 3fa33bb, MIT, see `statechart/LICENSE`),
with its TLC calls pointed at tla-rs:

- `scripts/run.ts` runs `tla-rs <main class> ...` where the skill ran
  `java -cp tla2tools.jar <main class> ...`. `TLA_RS` names the binary; without it, `tla-rs` is
  looked up on `PATH`. tla-rs's XMLExporter prints SANY's errors itself, so the skill no longer
  reruns `tla2sany.SANY` to get them.
- The tests that ran TLC run tla-rs when `TLA_RS` is set:

  ```sh
  cargo build --release -p tla-tools
  cd playground/statechart/scripts && npm install
  TLA_RS=$PWD/../../../target/release/tla-rs npm test
  ```

  `config-fuzz.test.ts` stays skipped: its oracle reads the config with TLC's Java classes.

The skill pins TLC 1.7.4 and tla-rs follows TLC 1.8.0, so these tests differ by version:
XMLExporter exits 2 on a spec it can't read (1.7.4 exits 1), and the extracted standard modules'
`tlc-<n>` folder changes with each run.
