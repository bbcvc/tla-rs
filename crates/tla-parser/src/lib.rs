//! Parses TLA+ modules with tree-sitter-tlaplus and lowers them into [`tla_ast`] trees, and parses
//! TLC model configuration (`.cfg`) files.

mod config;
mod expr;
mod lower;

pub use config::{
    ConfigError, ConfigValue, ConstantAssignment, ConstantSubstitution, ModelConfig, parse_config,
};

use tla_ast::{Module, Op, Span};
use tree_sitter::{Node, Parser, Tree};

use crate::lower::{Lower, expand_tabs, op_of};

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("line {line}, column {column}: {message}")]
pub struct ParseError {
    pub message: String,
    pub span: Span,
    pub line: usize,
    pub column: usize,
}

impl ParseError {
    pub(crate) fn new(source: &str, span: Span, message: impl Into<String>) -> Self {
        let (line, column) = span.line_column(source);
        Self { message: message.into(), span, line, column }
    }
}

/// Parses the first module in `source`. Text before and after the module is ignored, as SANY
/// ignores it.
pub fn parse_module(source: &str) -> Result<Module, ParseError> {
    parse_modules(source).map(|modules| modules.into_iter().next().expect("at least one module"))
}

/// Parses every top-level module in `source`, in order. A file can hold several, and SANY finds
/// a module in the file of an earlier one.
pub fn parse_modules(source: &str) -> Result<Vec<Module>, ParseError> {
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_tlaplus::LANGUAGE.into())
        .expect("the tree-sitter-tlaplus grammar matches the tree-sitter version");
    let expanded = expand_tabs(source);
    let text = expanded.as_ref().map_or(source, |(text, _)| text.as_str());
    let tree = parser
        .parse(text, None)
        .ok_or_else(|| ParseError::new(source, Span::default(), "the parser gave up"))?;
    let (tree, masks) = match tree.root_node().has_error() {
        true => reparse_operator_selectors(&mut parser, text, &tree).unwrap_or((tree, Vec::new())),
        false => (tree, Vec::new()),
    };
    let tabs = expanded.as_ref().map_or(&[][..], |(_, tabs)| tabs.as_slice());
    let lower = Lower { source, tabs, masks: &masks };
    let root = tree.root_node();
    let mut cursor = root.walk();
    let modules: Vec<_> =
        root.named_children(&mut cursor).filter(|child| child.kind() == "module").collect();
    if modules.is_empty() {
        let message = if root.is_error() { "syntax error" } else { "no module found" };
        return Err(ParseError::new(source, lower.span(root), message));
    }
    modules
        .into_iter()
        .map(|module| {
            if let Some(error) = first_error(module) {
                let message = if error.is_missing() {
                    format!("missing {}", error.kind())
                } else {
                    "syntax error".to_owned()
                };
                return Err(ParseError::new(source, lower.span(error), message));
            }
            lower.module(module)
        })
        .collect()
}

/// The grammar reads an operator symbol between the `!`s of a subexpression reference, as in
/// `COp2!lab!:!++!lab`, and at the end with arguments, as in `!++(4, 5)`, but not at the end
/// without them, as in `COp!@!++`, which SANY reads. When a parse fails, this replaces each
/// operator symbol after a `!` that could be such an end with an identifier of the same length,
/// and parses again.
/// It returns the new tree, with the operator each identifier stands for by its start, only if
/// the new tree has no errors and each identifier ends a reference, so no other error is repaired.
fn reparse_operator_selectors(
    parser: &mut Parser,
    text: &str,
    tree: &Tree,
) -> Option<(Tree, Vec<(usize, Op)>)> {
    let mut masks = Vec::new();
    collect_operator_selectors(tree.root_node(), text, &mut masks);
    if masks.is_empty() {
        return None;
    }
    let mut masked = text.as_bytes().to_vec();
    for (start, end, _) in &masks {
        masked[*start..*end].fill(b'x');
    }
    let masked = String::from_utf8(masked).ok()?;
    let reparsed = parser.parse(&masked, None)?;
    if reparsed.root_node().has_error() {
        return None;
    }
    let ends_reference = |&(start, end, _): &(usize, usize, Op)| {
        let node = reparsed.root_node().descendant_for_byte_range(start, end)?;
        let parent = node.parent()?;
        let op = parent.child_by_field_name("op")?;
        let is_last_part = node.kind() == "identifier_ref"
            && (node.start_byte(), node.end_byte()) == (start, end)
            && parent.kind() == "prefixed_op"
            && op.id() == node.id();
        is_last_part.then_some(())
    };
    masks
        .iter()
        .all(|mask| ends_reference(mask).is_some())
        .then(|| (reparsed, masks.into_iter().map(|(start, _, op)| (start, op)).collect()))
}

/// The operator symbols right after a `!` and not followed by `(` or `!`, which the grammar already
/// reads, as in `!++(4, 5)` and `!++!lab`. The grammar leaves the others in an `ERROR` node, or
/// reads them as infix operators of what follows.
fn collect_operator_selectors(node: Node, text: &str, masks: &mut Vec<(usize, usize, Op)>) {
    let bytes = text.as_bytes();
    if node.kind().ends_with("_op_symbol")
        && node.start_byte() > 0
        && bytes[node.start_byte() - 1] == b'!'
        && let Some(op) = op_of(node)
    {
        let next = bytes[node.end_byte()..].iter().find(|byte| !byte.is_ascii_whitespace());
        if !matches!(next, Some(b'(' | b'!')) {
            masks.push((node.start_byte(), node.end_byte(), op));
        }
        return;
    }
    let mut cursor = node.walk();
    for child in node.named_children(&mut cursor) {
        collect_operator_selectors(child, text, masks);
    }
}

fn first_error(node: Node) -> Option<Node> {
    if node.is_error() || node.is_missing() {
        return Some(node);
    }
    // SANY skips comments, so a PlusCal algorithm the grammar can't read in one is no error.
    if !node.has_error() || matches!(node.kind(), "block_comment" | "pcal_algorithm") {
        return None;
    }
    let mut cursor = node.walk();
    node.children(&mut cursor).find_map(first_error)
}
