//! `tla2sany.xml.XMLExporter`: SANY's semantic tree of a spec as XML, in the format of SANY's
//! schema (`sany.xsd`), as far as tools built on TLC read it.
//!
//! The export has an entry in `context` for each module, each `CONSTANT` and `VARIABLE`
//! declaration, and each definition at the top level of a module, with its location, SANY's
//! level, its name and its arity; and for each module, references to the declarations and
//! definitions it holds, the root module's being every one it can name. It leaves out the bodies
//! of the definitions, their parameters, and the built-in operators, and numbers the nodes in
//! the order SANY creates them rather than with SANY's numbers: the modules in the order SANY
//! analyzes them, and what each module holds in the order it is written. A tool that reads the
//! variables in the order of their numbers, as the statechart skill of cursor/plugins does, gets
//! SANY's order.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use tla_tools_ast::Span;
use tla_tools_checker::load::{self, Library};
use tla_tools_resolve::{DefId, ModuleId, RootName, Spec};

use crate::sany;

/// XMLExporter's exit statuses.
const SUCCESS: i32 = 0;
const ARGS_PARSING_FAILURE: i32 = 1;
const SPEC_PARSING_FAILURE: i32 = 2;
const UNREPRESENTABLE_CHARACTER: i32 = 7;

/// SANY's kinds of declarations.
const CONSTANT_KIND: u8 = 2;
const VARIABLE_KIND: u8 = 3;

const USAGE: &str = "Usage: tla2sany.xml.XMLExporter [-I dir]... [-o] [-r] [-t] [-u] [-help] FILE

Given a TLA+ file, parse that file with SANY then translate the module's semantic parse tree to
XML, including all the modules depended on. The XML is printed to stdout.

  -I dir  Use the directory to resolve module dependencies. Repeatable.
  -o      Offline mode; skip XML schema validation step.
  -r      Restrict mode; include only declarations and definitions of the specified module.
  -t      Terse; format XML output without tabs or newlines.
  -u      Accepted; tla-rs exports no comments.
";

/// What the command line asks for.
struct Options {
    file: String,
    includes: Vec<PathBuf>,
    is_terse: bool,
    is_restricted: bool,
}

/// XMLExporter reads the flags before the last argument, which names the module.
fn parse_args(args: &[String]) -> Result<Options, &'static str> {
    let Some((file, flags)) = args.split_last() else {
        return Err("at least one .tla file must be given");
    };
    let mut options =
        Options { file: file.clone(), includes: Vec::new(), is_terse: false, is_restricted: false };
    let mut flags = flags.iter();
    while let Some(flag) = flags.next() {
        match flag.as_str() {
            "-o" | "-u" => {}
            "-t" => options.is_terse = true,
            "-r" => options.is_restricted = true,
            "-I" => match flags.next() {
                Some(directory) => options.includes.push(PathBuf::from(directory)),
                None => {
                    return Err(
                        "the -I flag must be followed by a directory and at least one .tla file",
                    );
                }
            },
            _ => return Err("Only one TLA file to check allowed!"),
        }
    }
    Ok(options)
}

/// Runs XMLExporter with `args`, the arguments after its class name, and returns its exit
/// status.
pub fn main(args: &[String]) -> i32 {
    if args.last().is_some_and(|last| last == "-help") {
        print!("{USAGE}");
        return SUCCESS;
    }
    let options = match parse_args(args) {
        Ok(options) => options,
        Err(message) => {
            eprint!("ERROR: {message}\n{USAGE}");
            return ARGS_PARSING_FAILURE;
        }
    };
    let file = match options.file.ends_with(".tla") {
        true => options.file.clone(),
        false => format!("{}.tla", options.file),
    };
    // SANY looks for the module in the working directory, then in the -I directories.
    let path = std::iter::once(Path::new("."))
        .chain(options.includes.iter().map(PathBuf::as_path))
        .map(|directory| directory.join(&file))
        .find(|path| path.is_file())
        .unwrap_or_else(|| PathBuf::from(&file));
    let name = path.file_stem().unwrap_or_default().to_string_lossy().into_owned();
    let read = match load::load_spec(&path, &Library::new(&options.includes)) {
        Ok(mut read) => {
            without_warnings(&mut read.modules);
            read
        }
        Err(mut failure) => {
            without_warnings(&mut failure.modules);
            eprint!("{}", sany::rejected(&failure, &path, &name));
            eprintln!("ERROR: Failed to parse module.");
            return SPEC_PARSING_FAILURE;
        }
    };
    eprint!("{}", sany::accepted(&read.modules, &path));
    // SANY exports every string of every module, and refuses one with a character XML can't
    // hold.
    let modules = read.spec.modules.iter().map(|module| &*module.source);
    if let Some(char) = modules.filter_map(unrepresentable_in_strings).next() {
        eprintln!(
            "ERROR: The spec contains the character U+{:04X} in the StringValue element. XML 1.0 cannot represent that character in character data, not even as a numeric character reference, so the spec cannot be exported until the character is removed from it.",
            u32::from(char)
        );
        return UNREPRESENTABLE_CHARACTER;
    }
    let tree = export(&read.spec, &read.modules.order.analyzed, options.is_restricted);
    print!("{}", tree.print(options.is_terse));
    SUCCESS
}

/// An element of the XML: text, or other elements.
struct Element {
    tag: &'static str,
    text: Option<String>,
    children: Vec<Element>,
}

impl Element {
    fn new(tag: &'static str, children: Vec<Element>) -> Self {
        Self { tag, text: None, children }
    }

    fn text(tag: &'static str, text: impl ToString) -> Self {
        Self { tag, text: Some(text.to_string()), children: Vec::new() }
    }

    /// The document as Java's identity transformer writes it: indented by 2, or on one line.
    fn print(&self, is_terse: bool) -> String {
        let mut lines =
            vec![r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>"#.to_owned()];
        self.lines(0, if is_terse { 0 } else { 2 }, &mut lines);
        match is_terse {
            true => lines.concat(),
            false => lines.join("\n") + "\n",
        }
    }

    fn lines(&self, depth: usize, indent: usize, lines: &mut Vec<String>) {
        let margin = " ".repeat(depth * indent);
        let tag = self.tag;
        match &self.text {
            Some(text) if !text.is_empty() => {
                lines.push(format!("{margin}<{tag}>{}</{tag}>", escape(text)));
            }
            _ if self.children.is_empty() => lines.push(format!("{margin}<{tag}/>")),
            _ => {
                lines.push(format!("{margin}<{tag}>"));
                for child in &self.children {
                    child.lines(depth + 1, indent, lines);
                }
                lines.push(format!("{margin}</{tag}>"));
            }
        }
    }
}

/// Text escaped as Java's serializer escapes it.
fn escape(text: &str) -> String {
    let mut escaped = String::with_capacity(text.len());
    for char in text.chars() {
        match char {
            '&' => escaped.push_str("&amp;"),
            '<' => escaped.push_str("&lt;"),
            '>' => escaped.push_str("&gt;"),
            '\r' => escaped.push_str("&#13;"),
            char if u32::from(char) > 0xFFFF => {
                escaped.push_str(&format!("&#{};", u32::from(char)))
            }
            char => escaped.push(char),
        }
    }
    escaped
}

/// Whether XML 1.0 can hold `char` in character data, as its `Char` production says.
fn is_representable(char: char) -> bool {
    matches!(u32::from(char), 0x9 | 0xA | 0xD | 0x20..=0xD7FF | 0xE000..=0xFFFD | 0x10000..)
}

/// The first character in a string of the module `source` that XML 1.0 can't hold, outside the
/// comments.
fn unrepresentable_in_strings(source: &str) -> Option<char> {
    let mut chars = source.chars().peekable();
    let mut depth = 0usize;
    while let Some(char) = chars.next() {
        match char {
            '(' if chars.peek() == Some(&'*') => {
                chars.next();
                depth += 1;
            }
            '*' if depth > 0 && chars.peek() == Some(&')') => {
                chars.next();
                depth -= 1;
            }
            _ if depth > 0 => {}
            '\\' if chars.peek() == Some(&'*') => {
                for char in chars.by_ref() {
                    if char == '\n' {
                        break;
                    }
                }
            }
            '"' => {
                while let Some(char) = chars.next() {
                    match char {
                        '"' => break,
                        '\\' => drop(chars.next()),
                        char if !is_representable(char) => return Some(char),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
    None
}

/// A node of SANY's semantic tree that the export numbers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Node {
    Module(ModuleId),
    Constant(usize),
    Variable(usize),
    Definition(DefId),
}

/// The nodes of the export, numbered in the order SANY creates them.
struct Numbering<'a> {
    spec: &'a Spec,
    nodes: Vec<Node>,
    numbers: HashMap<Node, u32>,
}

impl Numbering<'_> {
    fn number(&mut self, node: Node) -> u32 {
        if let Some(&number) = self.numbers.get(&node) {
            return number;
        }
        let number = self.nodes.len() as u32 + 1;
        self.nodes.push(node);
        self.numbers.insert(node, number);
        number
    }

    /// Where a node is written, and the module it is written in.
    fn place(&self, node: Node) -> (ModuleId, Span) {
        let spec = self.spec;
        match node {
            Node::Module(module) => {
                (module, Span::new(0, spec.modules[module.index()].source.len()))
            }
            Node::Constant(index) => (spec.constants[index].module, spec.constants[index].span),
            Node::Variable(index) => (spec.variables[index].module, spec.variables[index].span),
            Node::Definition(def) => (spec.def(def).module, spec.def(def).span),
        }
    }
}

/// Whether `def` is an operator definition at the top level of the module whose text holds it,
/// rather than a statement of an `ASSUME` or a theorem.
fn is_top_level(spec: &Spec, def: DefId) -> bool {
    let definition = spec.def(def);
    definition.depth == 0
        && !definition.is_part
        && !definition.is_instantiated
        && !spec.statements.contains(&def)
}

/// The XML of `spec`, whose modules SANY analyzes in the order `analyzed` names them. With
/// `is_restricted`, the root module's own declarations and definitions alone.
fn export(spec: &Spec, analyzed: &[String], is_restricted: bool) -> Element {
    let root = ModuleId(0);
    let position = |module: ModuleId| {
        let name = spec.modules[module.index()].name.as_str();
        analyzed.iter().position(|known| known == name).unwrap_or(analyzed.len())
    };
    let mut modules: Vec<ModuleId> =
        (0..spec.modules.len()).map(|index| ModuleId(index as u32)).collect();
    modules.sort_by_key(|&module| position(module));
    if is_restricted {
        modules.retain(|&module| module == root);
    }
    // What each module holds, in the order it is written.
    let mut held: HashMap<ModuleId, Vec<Node>> = HashMap::new();
    let constants = (0..spec.constants.len()).map(Node::Constant);
    let variables = (0..spec.variables.len()).map(Node::Variable);
    let definitions = (0..spec.defs.len())
        .map(|index| DefId(index as u32))
        .filter(|&def| is_top_level(spec, def))
        .map(Node::Definition);
    let mut numbering = Numbering { spec, nodes: Vec::new(), numbers: HashMap::new() };
    for node in constants.chain(variables).chain(definitions) {
        held.entry(numbering.place(node).0).or_default().push(node);
    }
    for nodes in held.values_mut() {
        nodes.sort_by_key(|&node| numbering.place(node).1.start);
    }
    for &module in &modules {
        numbering.number(Node::Module(module));
        for &node in held.get(&module).into_iter().flatten() {
            numbering.number(node);
        }
    }
    // The root module can name what the modules it extends hold, as well as its own.
    let mut named: Vec<Node> = match is_restricted {
        true => held.get(&root).cloned().unwrap_or_default(),
        false => spec
            .root
            .values()
            .filter_map(|name| match *name {
                RootName::Var(var) => Some(Node::Variable(var.index())),
                RootName::Const(constant) => Some(Node::Constant(constant.index())),
                RootName::Def(def) => {
                    (!spec.statements.contains(&def)).then_some(Node::Definition(def))
                }
            })
            .collect(),
    };
    for &node in &named {
        numbering.number(node);
    }
    named.sort_by_key(|node| numbering.numbers[node]);
    let mut entries = Vec::new();
    for &node in &numbering.nodes {
        let element = match node {
            Node::Module(module) => {
                let nodes = match module == root {
                    true => named.clone(),
                    false => held.get(&module).cloned().unwrap_or_default(),
                };
                module_element(&numbering, module, &nodes)
            }
            _ => symbol_element(&numbering, node),
        };
        entries.push(Element::new(
            "entry",
            vec![Element::text("UID", numbering.numbers[&node]), element],
        ));
    }
    Element::new(
        "modules",
        vec![
            Element::text("RootModule", spec.modules[root.index()].name),
            Element::new("context", entries),
        ],
    )
}

/// SANY's location of a node: the lines and columns of its first and last characters, and its
/// module.
fn location(numbering: &Numbering<'_>, node: Node) -> Element {
    let (module, span) = numbering.place(node);
    let module = &numbering.spec.modules[module.index()];
    let source = &module.source;
    let text = source.get(span.start as usize..span.end as usize).unwrap_or_default();
    let end = span.start as usize + text.trim_end().len();
    let last = end.saturating_sub(1).max(span.start as usize);
    let (line, column) = span.line_column(source);
    let (end_line, end_column) = Span::new(last, last + 1).line_column(source);
    Element::new(
        "location",
        vec![
            Element::new(
                "column",
                vec![Element::text("begin", column), Element::text("end", end_column)],
            ),
            Element::new(
                "line",
                vec![Element::text("begin", line), Element::text("end", end_line)],
            ),
            Element::text("filename", module.name),
        ],
    )
}

/// A reference to a node by its number.
fn reference(numbering: &Numbering<'_>, node: Node) -> Element {
    let tag = match node {
        Node::Module(_) => "ModuleNodeRef",
        Node::Constant(_) | Node::Variable(_) => "OpDeclNodeRef",
        Node::Definition(_) => "UserDefinedOpKindRef",
    };
    Element::new(tag, vec![Element::text("UID", numbering.numbers[&node])])
}

fn module_element(numbering: &Numbering<'_>, module: ModuleId, nodes: &[Node]) -> Element {
    let name = numbering.spec.modules[module.index()].name;
    let mut children =
        vec![location(numbering, Node::Module(module)), Element::text("uniquename", name)];
    // SANY lists the declarations before the definitions.
    let is_declaration = |node: &&Node| matches!(node, Node::Constant(_) | Node::Variable(_));
    let declarations = nodes.iter().filter(is_declaration);
    let definitions = nodes.iter().filter(|node| !is_declaration(node));
    for &node in declarations.chain(definitions) {
        children.push(reference(numbering, node));
    }
    Element::new("ModuleNode", children)
}

fn symbol_element(numbering: &Numbering<'_>, node: Node) -> Element {
    let spec = numbering.spec;
    match node {
        Node::Constant(index) | Node::Variable(index) => {
            let (declaration, level, kind) = match node {
                Node::Constant(_) => (&spec.constants[index], 0, CONSTANT_KIND),
                _ => (&spec.variables[index], 1, VARIABLE_KIND),
            };
            Element::new(
                "OpDeclNode",
                vec![
                    location(numbering, node),
                    Element::text("level", level),
                    Element::text("uniquename", declaration.name),
                    Element::text("arity", declaration.arity),
                    Element::text("kind", kind),
                ],
            )
        }
        Node::Definition(def) => {
            let definition = spec.def(def);
            let module = Node::Module(definition.module);
            let mut children = vec![
                location(numbering, node),
                Element::text("level", spec.level(def).number()),
                Element::text("uniquename", definition.name),
                Element::text("arity", definition.params.len()),
            ];
            if numbering.numbers.contains_key(&module) {
                children.push(Element::new(
                    "originallyDefinedInModule",
                    vec![reference(numbering, module)],
                ));
            }
            Element::new("UserDefinedOpKind", children)
        }
        Node::Module(_) => unreachable!("a module is exported by module_element"),
    }
}

/// SANY prints its warnings only to the output XMLExporter leaves out, so it prints only SANY's
/// errors.
fn without_warnings(modules: &mut load::Modules) {
    modules.messages.retain(|message| !message.is_warning);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| arg.to_string()).collect()
    }

    #[test]
    fn reads_xml_exporter_s_arguments() {
        let options = parse_args(&args(&["-o", "-I", "lib", "-t", "Spec.tla"])).unwrap();
        assert_eq!(options.file, "Spec.tla");
        assert_eq!(options.includes, vec![PathBuf::from("lib")]);
        assert!(options.is_terse && !options.is_restricted);
        assert!(parse_args(&args(&["-I", "Spec.tla"])).is_err());
        assert!(parse_args(&args(&["A.tla", "B.tla"])).is_err());
        assert!(parse_args(&[]).is_err());
    }

    #[test]
    fn finds_a_character_xml_can_t_hold_in_a_string() {
        assert_eq!(unrepresentable_in_strings("S == \"red \u{1b}[31m\""), Some('\u{1b}'));
        assert_eq!(unrepresentable_in_strings("S == \"\\\" \u{1}\""), Some('\u{1}'));
        assert_eq!(unrepresentable_in_strings("(* \"\u{1b}\" *) \\* \"\u{1b}\"\nS == \"a\""), None);
        assert_eq!(unrepresentable_in_strings("S == \"tab\there\""), None);
    }

    #[test]
    fn prints_as_java_s_transformer_does() {
        let document = Element::new(
            "modules",
            vec![Element::text("RootModule", "M"), Element::new("context", Vec::new())],
        );
        assert_eq!(
            document.print(false),
            "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n<modules>\n  <RootModule>M</RootModule>\n  <context/>\n</modules>\n"
        );
        assert_eq!(escape("a < b & \u{1F600}"), "a &lt; b &amp; &#128512;");
    }
}
