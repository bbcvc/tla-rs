#!/usr/bin/env node
// Prepares the npm packages for a release, at the version in the workspace's Cargo.toml.
//
//   node npm/scripts/package.mjs platform <os-arch> <binary> <out-dir>
//       writes the package tla-rs-<os-arch> holding <binary> into <out-dir>
//   node npm/scripts/package.mjs main <out-dir>
//       writes the tla-rs package, which depends on every platform package, into <out-dir>

import { chmodSync, copyFileSync, cpSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { basename, dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..", "..");
const main = JSON.parse(readFileSync(join(root, "npm/tla-rs/package.json"), "utf8"));
const version = readFileSync(join(root, "Cargo.toml"), "utf8").match(
  /\[workspace\.package\][^[]*?\nversion\s*=\s*"([^"]+)"/
)[1];

// os-arch (as Node names them) -> package.json fields restricting where npm installs it
const PLATFORMS = {
  "darwin-arm64": { os: ["darwin"], cpu: ["arm64"] },
  "darwin-x64": { os: ["darwin"], cpu: ["x64"] },
  "linux-arm64": { os: ["linux"], cpu: ["arm64"], libc: ["glibc"] },
  "linux-x64": { os: ["linux"], cpu: ["x64"], libc: ["glibc"] },
  "win32-x64": { os: ["win32"], cpu: ["x64"] },
};

function write(dir, pkg) {
  mkdirSync(dir, { recursive: true });
  writeFileSync(join(dir, "package.json"), JSON.stringify(pkg, null, 2) + "\n");
  copyFileSync(join(root, "LICENSE"), join(dir, "LICENSE"));
}

const [command, ...args] = process.argv.slice(2);
if (command === "platform") {
  const [platform, binary, out] = args;
  const fields = PLATFORMS[platform];
  if (!fields || !binary || !out) throw new Error(`usage: platform <${Object.keys(PLATFORMS).join("|")}> <binary> <out-dir>`);
  mkdirSync(join(out, "bin"), { recursive: true });
  const exe = join(out, "bin", basename(binary));
  copyFileSync(binary, exe);
  chmodSync(exe, 0o755);
  write(out, {
    name: `tla-rs-${platform}`,
    version,
    description: `The tla-rs binary for ${platform}`,
    homepage: main.homepage,
    repository: main.repository,
    license: main.license,
    files: ["bin"],
    preferUnplugged: true,
    ...fields,
  });
} else if (command === "main") {
  const [out] = args;
  if (!out) throw new Error("usage: main <out-dir>");
  cpSync(join(root, "npm/tla-rs/bin"), join(out, "bin"), { recursive: true });
  copyFileSync(join(root, "README.md"), join(out, "README.md"));
  const optionalDependencies = Object.fromEntries(Object.keys(PLATFORMS).map((p) => [`tla-rs-${p}`, version]));
  write(out, { ...main, version, optionalDependencies });
} else {
  throw new Error("usage: package.mjs platform|main ...");
}
console.log(`${command} package ${version} written`);
