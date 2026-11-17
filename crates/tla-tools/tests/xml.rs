//! Runs `tla-rs tla2sany.xml.XMLExporter` as the statechart skill of cursor/plugins runs SANY's,
//! and compares what the skill reads of the XML with what it reads of SANY's.
//!
//! Each folder of `tests/statechart` holds a spec the skill checked, and in `sany.txt` what the
//! skill's `readSany` reads of the XML SANY exported for it (tla-ts `tests/fixtures/statechart`):
//! the root module, its variables in the order of their numbers, and each declaration and
//! definition the root module holds, with its level and arity. Definitions of instances,
//! `I!Op`, are left out: tla-rs doesn't export them.

use std::collections::HashMap;
use std::path::Path;
use std::process::Command;

/// An element of an XML document without attributes, as SANY's export is.
#[derive(Debug, Default)]
struct Element {
    tag: String,
    text: String,
    children: Vec<Element>,
}

impl Element {
    fn child(&self, tag: &str) -> Option<&Element> {
        self.children.iter().find(|child| child.tag == tag)
    }

    fn text_of(&self, tag: &str) -> &str {
        self.child(tag).map_or("", |child| child.text.as_str())
    }
}

fn unescape(text: &str) -> String {
    text.replace("&lt;", "<").replace("&gt;", ">").replace("&amp;", "&")
}

/// Parses `xml`, which has no attributes, comments, or character data sections.
fn parse(xml: &str) -> Element {
    let mut open = vec![Element::default()];
    let mut rest = xml;
    while let Some(start) = rest.find('<') {
        open.last_mut().unwrap().text.push_str(&unescape(&rest[..start]));
        let end = rest[start..].find('>').expect("a tag ends") + start;
        let tag = &rest[start + 1..end];
        rest = &rest[end + 1..];
        if tag.starts_with('?') {
            continue;
        }
        if let Some(_closed) = tag.strip_prefix('/') {
            let element = open.pop().unwrap();
            open.last_mut().unwrap().children.push(element);
        } else if let Some(empty) = tag.strip_suffix('/') {
            let element = Element { tag: empty.to_owned(), ..Element::default() };
            open.last_mut().unwrap().children.push(element);
        } else {
            open.push(Element { tag: tag.to_owned(), ..Element::default() });
        }
    }
    let mut document = open.pop().unwrap();
    document.children.pop().expect("a root element")
}

/// What the statechart skill's `readSany` reads of an export, as `sany.txt` writes it.
fn skill_view(xml: &str) -> String {
    let modules = parse(xml);
    let context = modules.child("context").expect("a context");
    let nodes: HashMap<&str, &Element> =
        context.children.iter().map(|entry| (entry.text_of("UID"), &entry.children[1])).collect();
    let root = modules.text_of("RootModule");
    let module = nodes
        .values()
        .find(|node| node.tag == "ModuleNode" && node.text_of("uniquename") == root)
        .expect("the root module");
    let mut lines = Vec::new();
    let mut variables = Vec::new();
    for reference in &module.children {
        if reference.tag != "OpDeclNodeRef" && reference.tag != "UserDefinedOpKindRef" {
            continue;
        }
        let uid = reference.text_of("UID");
        let node = nodes[uid];
        let name = node.text_of("uniquename");
        if name.contains('!') {
            continue;
        }
        let kind = node.text_of("kind");
        let mut line = format!(
            "{} {name} level={} arity={}",
            node.tag,
            node.text_of("level"),
            node.text_of("arity")
        );
        if !kind.is_empty() {
            line.push_str(&format!(" kind={kind}"));
        }
        lines.push(line);
        if node.tag == "OpDeclNode" && kind == "3" {
            variables.push((uid.parse::<u32>().unwrap(), name.to_owned()));
        }
    }
    variables.sort();
    lines.sort();
    let variables: Vec<String> = variables.into_iter().map(|(_, name)| name).collect();
    let mut view = vec![format!("root {root}"), format!("variables {}", variables.join(" "))];
    view.extend(lines);
    view.join("\n") + "\n"
}

/// Exports the spec `name` in `directory` as the skill does, from another directory.
fn export(directory: &Path, name: &str) -> (i32, String) {
    let file = directory.join(format!("{name}.tla"));
    let output = Command::new(env!("CARGO_BIN_EXE_tla-rs"))
        .args(["tla2sany.xml.XMLExporter", "-o", "-I"])
        .arg(directory)
        .arg(&file)
        .current_dir(std::env::temp_dir())
        .output()
        .expect("tla-rs runs");
    (output.status.code().unwrap(), String::from_utf8(output.stdout).unwrap())
}

#[test]
fn exports_what_the_statechart_skill_reads_as_sany_does() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/statechart");
    let mut directories: Vec<_> = std::fs::read_dir(&root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.join("sany.txt").is_file())
        .collect();
    directories.sort();
    assert!(directories.len() >= 30, "the statechart fixtures are there");
    let mut failures = Vec::new();
    for directory in directories {
        let name = directory.file_name().unwrap().to_string_lossy().into_owned();
        let (status, xml) = export(&directory, &name);
        if status != 0 {
            failures.push(format!("{name}: exit {status}"));
            continue;
        }
        let expected = std::fs::read_to_string(directory.join("sany.txt")).unwrap();
        let view = skill_view(&xml);
        if view != expected {
            failures.push(format!("{name}:\n{view}\nSANY:\n{expected}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn reports_a_spec_sany_rejects() {
    let directory = std::env::temp_dir().join(format!("tla-rs-xml-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source = "---- MODULE Rejected ----\nVARIABLE x\nNext == y' = 1\n====\n";
    std::fs::write(directory.join("Rejected.tla"), source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_tla-rs"))
        .args(["tla2sany.xml.XMLExporter", "-o", "Rejected.tla"])
        .current_dir(&directory)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let errors = String::from_utf8(output.stderr).unwrap();
    assert!(errors.contains("Unknown operator: `y'."), "{errors}");
    assert!(errors.ends_with("ERROR: Failed to parse module.\n"), "{errors}");
}

#[test]
fn leaves_out_theorems_and_assumptions() {
    let directory = std::env::temp_dir().join(format!("tla-rs-xml-thm-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source = "---- MODULE Statements ----\nCONSTANT N\nVARIABLES y, x\nASSUME Named == N \\in {1}\nASSUME N = N\nTHEOREM T == N = N\nOp == x\n====\n";
    std::fs::write(directory.join("Statements.tla"), source).unwrap();
    let (status, xml) = export(&directory, "Statements");
    assert_eq!(status, 0);
    assert_eq!(
        skill_view(&xml),
        "root Statements\nvariables y x\nOpDeclNode N level=0 arity=0 kind=2\nOpDeclNode x level=1 arity=0 kind=3\nOpDeclNode y level=1 arity=0 kind=3\nUserDefinedOpKind Op level=1 arity=0\n"
    );
}
