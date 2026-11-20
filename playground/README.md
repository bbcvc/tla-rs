# Playground

Tools built on TLC, run on tla-rs instead.

## statechart

`statechart/` is the statechart skill of [cursor/plugins](https://github.com/cursor/plugins)
(`harness/pstack/claude-code/skills/statechart`, at 3fa33bb, MIT, see `statechart/LICENSE`). It
checks a TLA+ model and draws it as a Mermaid statechart, with the shortest path to each state that
breaks a rule. Here it runs tla-rs in place of `java -cp tla2tools.jar`:

```sh
cargo install --path crates/tla-tools        # or set TLA_RS to target/release/tla-rs
playground/statechart/scripts/statechart Spec.tla --out out/
```

`example/` is a checkout whose payment can time out. The bank's callback that marks an order paid
is queued when the bank takes the money and can reach the shop after the order was cancelled and
its money refunded, so the order ships with its money refunded. `CheckoutFixed.tla` leaves a
cancelled order cancelled, and the rule holds:

```sh
playground/statechart/scripts/statechart playground/example/Checkout.tla \
  --view playground/example/view.mjs --out /tmp/checkout        # exit 1: NeverShipRefunded breaks
playground/statechart/scripts/statechart playground/example/CheckoutFixed.tla \
  --view playground/example/view.mjs --out /tmp/checkout-fixed  # exit 0
```

The report gives the shortest path to the bug: you place the order, the bank takes the money, the
payment times out, the refund job gives the money back, the bank's callback arrives, the warehouse
ships. `statechart/references/render.md` renders `chart.mmd` as SVG.

### What changed from the skill

- `scripts/run.ts` runs `tla-rs <main class> ...` where the skill ran
  `java -cp tla2tools.jar <main class> ...`. `TLA_RS` names the binary; without it, `tla-rs` is
  looked up on `PATH`. tla-rs's XMLExporter prints SANY's errors itself, so the skill no longer
  reruns `tla2sany.SANY` to get them.
- `scripts/frontends/dot.ts` drops an action's arguments from a step's label. TLC 1.8.0, which
  tla-rs follows, labels a step `RMPrepare(r1)`; the skill was written for TLC 1.7.4's
  `RMPrepare`, and groups steps by action.
- The tests that ran TLC run tla-rs when `TLA_RS` is set. `config-fuzz.test.ts` stays skipped:
  its oracle reads the config with TLC's Java classes.
- TLC 1.8.0 differs from 1.7.4 in two places the tests see: XMLExporter exits 2 on a spec it can't
  read (1.7.4 exits 1), and the folder the standard modules are extracted to changes with each run.
  `CounterGuard` and `TypeGuard` are recorded again from tla-rs, for 1.8.0's words for a tuple
  applied out of its domain.

### Tests

```sh
cd playground/statechart/scripts && npm install --no-package-lock
npm test                                                    # replays the recorded runs
TLA_RS=$PWD/../../../target/release/tla-rs npm test         # runs tla-rs
```

With tla-rs, 369 of 373 pass and one is skipped. Three fail:

- Two are tla-rs's gaps in SANY's errors: a syntax error is not in SANY's words, and only the first
  of twelve semantic errors is reported.
- The launcher reached through two symlinks fails on macOS, where the temp folder is itself a
  symlink. It fails the same way in the skill itself.
