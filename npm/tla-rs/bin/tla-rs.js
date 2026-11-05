#!/usr/bin/env node
// Runs the prebuilt tla-rs binary for this platform, installed as an optional dependency.
"use strict";

const { spawnSync } = require("node:child_process");
const path = require("node:path");

function binaryPath() {
  if (process.env.TLA_RS_BINARY) return process.env.TLA_RS_BINARY;
  const pkg = `tla-rs-${process.platform}-${process.arch}`;
  const exe = process.platform === "win32" ? "tla-rs.exe" : "tla-rs";
  try {
    return require.resolve(`${pkg}/bin/${exe}`);
  } catch {
    console.error(
      `tla-rs: no prebuilt binary for ${process.platform}-${process.arch} (package ${pkg} is not installed).\n` +
        "If your package manager skipped optional dependencies, reinstall without --no-optional.\n" +
        "Otherwise install from source with `cargo install tla-tools`, " +
        "or set TLA_RS_BINARY to the path of a tla-rs binary."
    );
    process.exit(1);
  }
}

const result = spawnSync(binaryPath(), process.argv.slice(2), { stdio: "inherit" });
if (result.error) {
  console.error(`tla-rs: ${result.error.message}`);
  process.exit(1);
}
if (result.signal) {
  process.kill(process.pid, result.signal);
} else {
  process.exit(result.status);
}
