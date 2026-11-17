//! TLC's `-dump` of the states it finds, ported from tla-ts `state-graph.ts`: TLC's
//! `tlc2.util.StateWriter`, which lists each distinct state, and its `DotStateWriter`, which
//! writes the state graph in DOT with an edge for each step, as TLC 1.8.0 writes them.
//!
//! The graph names each state by TLC's 64-bit fingerprint of it, and ranks the states by the
//! level the search expanded them at. TLC keeps the ranks and the colors of the actions in Java
//! hash maps, and writes them in the order the maps iterate in, which [`java_hash_order`] gives.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::PathBuf;

/// What TLC's `-dump [dot[,colorize][,actionlabels][,snapshot]] file` asks for.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Dump {
    /// The file to write, with its extension.
    pub path: PathBuf,
    /// Write the state graph in DOT, not a list of the states.
    pub dot: bool,
    /// Color each edge by its action, and add a legend of the actions.
    pub colorize: bool,
    /// Label each edge with its action and the values of the action's parameters.
    pub action_labels: bool,
    /// Also keep the graph so far, closed, in `<file>_snapshot.dot`.
    pub snapshot: bool,
}

impl Dump {
    /// Whether the graph shows the action of each step, which the search then generates the
    /// successors of a state action by action to know.
    pub fn names_edges(&self) -> bool {
        self.dot && (self.colorize || self.action_labels)
    }

    /// Where the snapshot of the graph goes.
    fn snapshot_path(&self) -> PathBuf {
        PathBuf::from(self.path.to_string_lossy().replace(".dot", "_snapshot.dot"))
    }
}

/// A state as the graph shows it: TLC's fingerprint of it, and the state as TLC prints it with
/// its `ALIAS` and without.
pub struct Node<'a> {
    pub fingerprint: i64,
    pub label: &'a str,
    pub text: &'a str,
}

/// The action of a step, as TLC names it in the graph: its name, which TLC colors the edge by,
/// and its name with the values of its parameters, `Request(0)`, which labels the edge.
pub struct Edge<'a> {
    pub name: &'a str,
    pub signature: &'a str,
}

/// The scheme of TLC's colors of the edges.
const COLOR_SCHEME: &str = "paired12";

/// Writes the states the search finds to the file of a [`Dump`] as it finds them.
pub struct Writer {
    dump: Dump,
    out: BufWriter<File>,
    /// How many states a plain dump lists.
    states: u64,
    /// The fingerprints of the states expanded at each level, the levels in the order they
    /// were first ranked and each level's states in the order they were first ranked.
    ranks: Vec<(u32, Vec<i64>)>,
    ranked: HashMap<u32, (usize, HashSet<i64>)>,
    /// The color of each action, by name, numbered from 2 in the order the actions were found.
    colors: Vec<String>,
    color_of: HashMap<String, usize>,
    /// The first error writing the file.
    error: Option<io::Error>,
}

impl fmt::Debug for Writer {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_struct("Writer").field("dump", &self.dump).finish_non_exhaustive()
    }
}

impl Writer {
    /// Creates the file and writes the start of the graph, as TLC does when it starts.
    pub fn create(dump: Dump) -> io::Result<Self> {
        let out = BufWriter::new(File::create(&dump.path)?);
        let mut writer = Self {
            dump,
            out,
            states: 0,
            ranks: Vec::new(),
            ranked: HashMap::new(),
            colors: Vec::new(),
            color_of: HashMap::new(),
            error: None,
        };
        if writer.dump.dot {
            let edge = match writer.dump.colorize {
                true => format!("edge [colorscheme=\"{COLOR_SCHEME}\"]\n"),
                false => String::new(),
            };
            let header = format!(
                "strict digraph DiskGraph {{\nnode [shape=box,style=rounded]\n{edge}nodesep=0.35;\nsubgraph cluster_graph {{\ncolor=\"white\";\n"
            );
            writer.write(&header);
        }
        Ok(writer)
    }

    /// The dump this writer writes.
    pub fn dump(&self) -> &Dump {
        &self.dump
    }

    fn write(&mut self, text: &str) {
        if self.error.is_none()
            && let Err(error) = self.out.write_all(text.as_bytes())
        {
            self.error = Some(error);
        }
    }

    /// Lists a state in a plain dump.
    fn list(&mut self, state: &Node<'_>) {
        self.states += 1;
        let text = format!("State {}:\n{}\n", self.states, state.text);
        self.write(&text);
    }

    /// Ranks the state with this fingerprint at `level`.
    fn rank(&mut self, level: u32, fingerprint: i64) {
        let (index, seen) = self.ranked.entry(level).or_insert_with(|| {
            self.ranks.push((level, Vec::new()));
            (self.ranks.len() - 1, HashSet::new())
        });
        if seen.insert(fingerprint) {
            self.ranks[*index].1.push(fingerprint);
        }
    }

    /// The color TLC gives the edges of an action: 1 without one.
    fn color(&mut self, edge: Option<&Edge<'_>>) -> usize {
        let Some(edge) = edge else { return 1 };
        if let Some(&color) = self.color_of.get(edge.name) {
            return color;
        }
        let color = self.colors.len() + 2;
        self.colors.push(edge.name.to_owned());
        self.color_of.insert(edge.name.to_owned(), color);
        color
    }

    /// An initial state the search found new.
    pub fn initial_state(&mut self, state: &Node<'_>) {
        if !self.dump.dot {
            return self.list(state);
        }
        let line = format!(
            "{} [label=\"{}\",style = filled]\n",
            state.fingerprint,
            dot_label(state.label)
        );
        self.write(&line);
        self.rank(1, state.fingerprint);
    }

    /// The step from `state`, expanded at `level`, to `successor`, which the search found new
    /// unless `is_seen`, by `edge` if the graph names its edges.
    pub fn successor(
        &mut self,
        state: i64,
        level: u32,
        successor: &Node<'_>,
        is_seen: bool,
        edge: Option<&Edge<'_>>,
    ) {
        if !self.dump.dot {
            if !is_seen {
                self.list(successor);
            }
            return;
        }
        let color = match self.dump.colorize {
            true => self.color(edge).to_string(),
            false => "black".to_owned(),
        };
        let label = match (self.dump.action_labels, edge) {
            (true, Some(edge)) => escape(edge.signature),
            _ => String::new(),
        };
        let mut lines = format!(
            "{state} -> {} [label=\"{label}\",color=\"{color}\",fontcolor=\"{color}\"];\n",
            successor.fingerprint
        );
        if !is_seen {
            lines.push_str(&format!(
                "{} [label=\"{}\",tooltip=\"{}\"];\n",
                successor.fingerprint,
                dot_label(successor.label),
                dot_label(successor.text)
            ));
        }
        self.write(&lines);
        self.rank(level, state);
    }

    /// The end of the graph: the states of each rank, and the legend of the actions' colors.
    fn ending(&self) -> String {
        let mut ending = String::new();
        let levels: Vec<usize> = (0..self.ranks.len()).collect();
        for index in java_hash_order(&levels, |&index| self.ranks[index].0 as i32) {
            let states =
                java_hash_order(&self.ranks[index].1, |&fingerprint| long_hash(fingerprint));
            let states: String =
                states.iter().map(|fingerprint| format!("{fingerprint};")).collect();
            ending.push_str(&format!("{{rank = same; {states}}}\n"));
        }
        ending.push_str("}\n");
        if self.dump.colorize && self.colors.len() > 1 {
            ending.push_str(&format!(
                "subgraph cluster_legend {{graph[style=bold];label = \"Next State Actions\" style=\"solid\"\nnode [ labeljust=\"l\",colorscheme=\"{COLOR_SCHEME}\",style=filled,shape=record ]\n"
            ));
            for name in java_hash_order(&self.colors, |name| string_hash(name)) {
                let node = name.replace('!', ":");
                ending.push_str(&format!(
                    "{node} [label=\"{name}\",fillcolor={}]\n",
                    self.color_of[name.as_str()]
                ));
            }
            ending.push('}');
        }
        ending.push('}');
        ending
    }

    /// Writes the graph so far, closed, to the snapshot file, for a dump that asks for one.
    pub fn snapshot(&mut self) -> io::Result<()> {
        if !(self.dump.dot && self.dump.snapshot) {
            return Ok(());
        }
        self.out.flush()?;
        let snapshot = self.dump.snapshot_path();
        std::fs::copy(&self.dump.path, &snapshot)?;
        let mut file = std::fs::OpenOptions::new().append(true).open(&snapshot)?;
        file.write_all(self.ending().as_bytes())
    }

    /// Ends the graph and closes the file, as TLC does once the search is done.
    pub fn close(mut self) -> io::Result<()> {
        if self.dump.dot {
            let ending = self.ending();
            self.write(&ending);
        }
        if let Some(error) = self.error.take() {
            return Err(error);
        }
        self.out.flush()?;
        if self.dump.dot && self.dump.snapshot {
            std::fs::copy(&self.dump.path, self.dump.snapshot_path())?;
        }
        Ok(())
    }
}

/// TLC's `DotStateWriter.dotEscape`: backslashes and quotes escaped, and the text trimmed as
/// Java's `String.trim` does.
fn escape(text: &str) -> String {
    text.replace('\\', "\\\\").replace('"', "\\\"").trim_matches(|char| char <= ' ').to_owned()
}

/// A state as a DOT label: escaped, with each line break written `\n`.
fn dot_label(text: &str) -> String {
    escape(text).replace('\n', "\\n")
}

/// Java's `Long.hashCode`.
fn long_hash(value: i64) -> i32 {
    (value ^ ((value as u64) >> 32) as i64) as i32
}

/// Java's `String.hashCode`, over the UTF-16 code units of the string.
fn string_hash(text: &str) -> i32 {
    text.encode_utf16().fold(0i32, |hash, unit| hash.wrapping_mul(31).wrapping_add(i32::from(unit)))
}

/// The order a `java.util.HashMap` iterates over keys put in this order, with these hash codes:
/// by bucket, and in the order they were put within a bucket. The map doubles its 16 buckets
/// while it holds more keys than three quarters of them.
fn java_hash_order<T: Clone>(keys: &[T], hash: impl Fn(&T) -> i32) -> Vec<T> {
    let mut capacity = 16usize;
    while keys.len() * 4 > capacity * 3 {
        capacity *= 2;
    }
    let mask = capacity - 1;
    let bucket = |key: &T| {
        let hash = hash(key) as u32;
        ((hash ^ (hash >> 16)) as usize) & mask
    };
    let mut ordered: Vec<(usize, &T)> = keys.iter().map(|key| (bucket(key), key)).collect();
    ordered.sort_by_key(|(bucket, _)| *bucket);
    ordered.into_iter().map(|(_, key)| key.clone()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hashes_as_java_does() {
        assert_eq!(string_hash("Next"), 2_424_595);
        assert_eq!(string_hash(""), 0);
        assert_eq!(long_hash(1), 1);
        assert_eq!(long_hash(-1), 0);
        assert_eq!(long_hash(1 << 32), 1);
    }

    #[test]
    fn orders_keys_by_bucket_then_as_put() {
        assert_eq!(java_hash_order(&[17, 1, 16, 0], |&key| key), vec![16, 0, 17, 1]);
        // With 13 keys the map has 32 buckets.
        let keys: Vec<i32> = (0..13).map(|key| key * 16).collect();
        let ordered = java_hash_order(&keys, |&key| key);
        assert_eq!(&ordered[..4], &[0, 32, 64, 96]);
    }

    #[test]
    fn escapes_labels_as_tlc_does() {
        assert_eq!(dot_label("/\\ x = \"a\"\n/\\ y = 1\n"), "/\\\\ x = \\\"a\\\"\\n/\\\\ y = 1");
    }
}
