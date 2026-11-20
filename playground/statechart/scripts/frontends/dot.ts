import { type Graph, type State, type Step, type Value, type Vars } from "../ir.ts";
import { parseValue } from "./value.ts";

const unescapeDot = (s: string) => {
  let i = s.indexOf("\\");
  if (i === -1) return s;
  let out = "";
  let from = 0;
  for (; i !== -1 && i + 1 < s.length; i = s.indexOf("\\", i)) {
    const c = s[i + 1];
    if (c === "\n" || c === "\r" || c === "\u2028" || c === "\u2029") {
      i++;
      continue;
    }
    out += s.slice(from, i) + (c === "n" ? "\n" : c);
    i += 2;
    from = i;
  }
  return out + s.slice(from);
};

export const parseState = (label: string, parsed = new Map<string, [string, Value]>()): Vars => {
  const pairs: [string, Value][] = [];
  for (const part of (label.startsWith("/\\ ") ? label.slice(3) : label).split("\n/\\ ")) {
    let pair = parsed.get(part);
    if (!pair) {
      const [, name, value] = /^(\w+)\s*=\s*([\s\S]*)$/.exec(part) ?? [];
      if (!name) throw new Error(`cannot read the TLC state line "${part}"`);
      parsed.set(part, (pair = [name, parseValue(value)]));
    }
    pairs.push(pair);
  }
  return Object.fromEntries(pairs);
};

export type Lines = string | Iterable<string>;

export const linesOf = (input: Lines) => (typeof input === "string" ? input.split("\n") : input);

export function parseDot(input: Lines): Graph {
  const states = new Map<string, State>();
  const steps = new Map<string, Step>();
  const parsed = new Map<string, [string, Value]>();
  const owned = new Map<string, string>();
  const own = (s: string) => {
    let copy = owned.get(s);
    if (copy === undefined) owned.set((copy = String(JSON.parse(JSON.stringify(s)))), copy);
    return copy;
  };
  for (const line of linesOf(input)) {
    const edge = /^(-?\d+) -> (-?\d+) \[label="((?:[^"\\]|\\.)*)"/.exec(line);
    if (edge) {
      // TLC 1.8.0 labels a step with its action's arguments, as RMPrepare(r1). The chart
      // groups steps by action, as TLC 1.7.4 labels them, so one step per action is kept.
      const action = edge[3].replace(/\(.*$/s, "");
      steps.set(`${edge[1]} ${edge[2]} ${action}`, {
        from: own(edge[1]),
        to: own(edge[2]),
        action: own(action),
      });
      continue;
    }
    const node = /^(-?\d+) \[label="((?:[^"\\]|\\.)*)"(,style = filled)?/.exec(line);
    if (node)
      states.set(own(node[1]), {
        vars: parseState(unescapeDot(node[2]), parsed),
        start: !!node[3],
        breaks: [],
      });
  }
  for (const loose of steps.values())
    if (!states.has(loose.from) || !states.has(loose.to))
      throw new Error(
        `The TLC graph dump has a step ${loose.action} to or from a state that it does not list.`,
      );
  return { states, steps: [...steps.values()] };
}
