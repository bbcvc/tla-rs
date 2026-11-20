// A dev server that runs the statechart skill on tla-rs for the page.
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { defineConfig } from "vite";

const here = path.dirname(fileURLToPath(import.meta.url));
const repo = path.resolve(here, "../..");
const statechart = path.join(repo, "playground/statechart/scripts/statechart");
const built = path.join(repo, "target/release/tla-rs");
const tlaRs = process.env.TLA_RS || (fs.existsSync(built) ? built : "tla-rs");

// Each example is a folder of specs: a spec is Name.tla with Name.cfg beside it. A folder's
// view.mjs, and its other .tla files, go with each of its specs.
const sources = [
  { group: "Examples", dir: path.join(repo, "playground/example") },
  ...fs
    .readdirSync(path.join(repo, "playground/statechart/scripts/test/corpus"))
    .sort()
    .map((name) => ({
      group: "Skill corpus",
      dir: path.join(repo, "playground/statechart/scripts/test/corpus", name),
    })),
];

function examples() {
  const found = [];
  for (const { group, dir } of sources) {
    const files = fs.readdirSync(dir);
    const read = (f) => fs.readFileSync(path.join(dir, f), "utf8");
    const view = files.includes("view.mjs") ? read("view.mjs") : "";
    const modules = Object.fromEntries(
      files.filter((f) => f.endsWith(".tla")).map((f) => [f.slice(0, -4), read(f)]),
    );
    for (const f of files.sort()) {
      if (!f.endsWith(".cfg")) continue;
      const name = f.slice(0, -4);
      if (!(name in modules)) continue;
      const others = { ...modules };
      delete others[name];
      found.push({ group, name, tla: modules[name], cfg: read(f), view, others });
    }
  }
  return found;
}

const run = (args, options) =>
  new Promise((resolve) => {
    const child = spawn(statechart, args, options);
    let stderr = "";
    child.stderr.on("data", (chunk) => (stderr += chunk));
    child.stdout.resume();
    child.on("error", (error) => resolve({ code: 2, stderr: error.message }));
    child.on("close", (code) => resolve({ code, stderr }));
  });

async function check({ name, tla, cfg, view, others = {} }) {
  if (!/^[A-Za-z]\w*$/.test(name)) throw new Error(`${name} is not a module name.`);
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "tla-rs-playground-"));
  try {
    for (const [module, text] of Object.entries(others))
      if (/^[A-Za-z]\w*$/.test(module)) fs.writeFileSync(path.join(dir, `${module}.tla`), text);
    fs.writeFileSync(path.join(dir, `${name}.tla`), tla);
    fs.writeFileSync(path.join(dir, `${name}.cfg`), cfg);
    const args = [path.join(dir, `${name}.tla`), "--out", path.join(dir, "out")];
    if (view.trim()) {
      fs.writeFileSync(path.join(dir, "view.mjs"), view);
      args.push("--view", path.join(dir, "view.mjs"));
    }
    const started = performance.now();
    const { code, stderr } = await run(args, {
      cwd: dir,
      env: { ...process.env, TLA_RS: tlaRs },
    });
    const ms = Math.round(performance.now() - started);
    const out = (f) => {
      const file = path.join(dir, "out", f);
      return fs.existsSync(file) ? fs.readFileSync(file, "utf8") : "";
    };
    return { exit: code, ms, stderr, report: out("report.md"), chart: out("chart.mmd"), tlc: out("tlc.out") };
  } finally {
    fs.rmSync(dir, { recursive: true, force: true });
  }
}

const api = {
  name: "statechart-api",
  configureServer(server) {
    server.middlewares.use("/api/examples", (_req, res) => {
      res.setHeader("content-type", "application/json");
      res.end(JSON.stringify({ tlaRs, examples: examples() }));
    });
    server.middlewares.use("/api/check", (req, res) => {
      let body = "";
      req.on("data", (chunk) => (body += chunk));
      req.on("end", async () => {
        res.setHeader("content-type", "application/json");
        try {
          res.end(JSON.stringify(await check(JSON.parse(body))));
        } catch (error) {
          res.statusCode = 400;
          res.end(JSON.stringify({ error: String(error.message ?? error) }));
        }
      });
    });
  },
};

export default defineConfig({ plugins: [api], server: { port: 5178 } });
