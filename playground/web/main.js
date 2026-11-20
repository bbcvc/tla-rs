import { render } from "pele";

const $ = (id) => document.getElementById(id);
let examples = [];
let current;
let tab = "tla";

function load(index) {
  current = structuredClone(examples[index]);
  try { localStorage.setItem("example", current.group + "/" + current.name); } catch {}
  showTab(tab);
}

function showTab(name) {
  tab = name;
  for (const b of $("tabs").children) b.classList.toggle("active", b.dataset.tab === name);
  $("source").value = current[name];
}

function showOut(name) {
  for (const b of $("outs").children) b.classList.toggle("active", b.dataset.out === name);
  for (const id of ["chart", "report", "mermaid", "tlc"]) $(id).hidden = id !== name;
}

async function check() {
  current[tab] = $("source").value;
  $("status").textContent = "checking…";
  $("status").className = "";
  $("check").disabled = true;
  try {
    const r = await (await fetch("/api/check", { method: "POST", body: JSON.stringify(current) })).json();
    if (r.error) throw new Error(r.error);
    const verdict = { 0: "every rule holds", 1: "a rule breaks", 2: "TLC stopped" }[r.exit] ?? `exit ${r.exit}`;
    $("status").textContent = `${verdict} · exit ${r.exit} · ${r.ms} ms`;
    $("status").className = r.exit === 0 ? "ok" : r.exit === 1 ? "bad" : "error";
    $("report").textContent = r.report || r.stderr;
    $("mermaid").textContent = r.chart || "(no chart.mmd)";
    $("tlc").textContent = r.tlc;
    if (r.chart) {
      try {
        const out = render(r.chart, { limit: 1_000_000, outputLimit: 8_000_000, maxEdges: 10_000 });
        $("chart").innerHTML = typeof out === "string" ? out : out.svg;
      } catch (error) {
        $("chart").innerHTML = `<pre class="error"></pre>`;
        $("chart").firstChild.textContent = `Pele could not render the chart: ${error.message}`;
      }
      showOut("chart");
    } else {
      $("chart").innerHTML = "";
      $("chart").append(Object.assign(document.createElement("pre"), { textContent: r.stderr || "No chart: see the report." }));
      showOut(r.report ? "report" : "chart");
    }
  } catch (error) {
    $("status").textContent = error.message;
    $("status").className = "error";
  } finally {
    $("check").disabled = false;
  }
}

const { tlaRs, examples: list } = await (await fetch("/api/examples")).json();
examples = list;
$("engine").textContent = `engine: ${tlaRs}`;
const groups = new Map();
examples.forEach((e, i) => {
  if (!groups.has(e.group)) groups.set(e.group, Object.assign(document.createElement("optgroup"), { label: e.group }));
  groups.get(e.group).append(new Option(e.name, i));
});
$("example").append(...groups.values());
let saved;
try { saved = localStorage.getItem("example"); } catch {}
const start = Math.max(0, examples.findIndex((e) => e.group + "/" + e.name === saved));
$("example").value = start;
load(start);

$("example").onchange = () => { load(Number($("example").value)); check(); };
$("source").oninput = () => (current[tab] = $("source").value);
$("tabs").onclick = (e) => e.target.dataset.tab && showTab(e.target.dataset.tab);
$("outs").onclick = (e) => e.target.dataset.out && showOut(e.target.dataset.out);
$("check").onclick = check;
document.addEventListener("keydown", (e) => {
  if ((e.metaKey || e.ctrlKey) && e.key === "Enter") { e.preventDefault(); check(); }
});
check();
