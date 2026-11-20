//! Parses TLA+ modules with tree-sitter-tlaplus and lowers them into [`tla_tools_ast`] trees, and parses
//! TLC model configuration (`.cfg`) files.

mod config;
mod expr;
mod lower;
mod sany;

pub use config::{
    ConfigError, ConfigValue, ConstantAssignment, ConstantSubstitution, ModelConfig, parse_config,
};

use tla_tools_ast::{Module, Op, Span};
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

    /// What SANY prints for the module `source` this error is in: the report of SANY's own
    /// parser, or where SANY's parser would accept the module, as for an error SANY finds
    /// after parsing or a construct the grammar doesn't read, this error's message at its
    /// position under SANY's heading.
    pub fn sany_report(&self, source: &str) -> String {
        sany::parse_error(source).unwrap_or_else(|| {
            format!(
                "***Parse Error***\n{} at line {}, column {}\n",
                self.message, self.line, self.column
            )
        })
    }
}

/// What SANY reports for a module its lexer or parser rejects, in SANY's words: the
/// `***Parse Error***` report of `TLAplusParser`, or the lexer's error. `None` if SANY's parser
/// accepts the module.
pub fn sany_parse_error(source: &str) -> Option<String> {
    sany::parse_error(source)
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
        true => reparse_masked(&mut parser, text, &tree).unwrap_or((tree, Vec::new())),
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

/// When a parse fails, this replaces what the grammar can't read but SANY can with identifiers
/// of the same length, and parses again:
///
/// - The grammar reads an operator symbol between the `!`s of a subexpression reference, as in
///   `COp2!lab!:!++!lab`, and at the end with arguments, as in `!++(4, 5)`, but not at the end
///   without them, as in `COp!@!++`, which SANY reads. Each operator symbol after a `!` that
///   could be such an end is replaced.
/// - The grammar takes `Nat`, `Int`, `Real`, `STRING`, `BOOLEAN`, `TRUE`, and `FALSE` for its
///   keywords where an expression can start, so it can't read one as the first field of a
///   record, as in `[Nat |-> 1]` or `[TRUE : S]`, while SANY reads them as identifiers. Each such
///   field is replaced; lowering reads its name from the original text.
///
/// It returns the new tree, with the operator each identifier for an operator symbol stands for
/// by its start, only if the new tree has no errors and each identifier ends a reference or names
/// a field, so no other error is repaired.
fn reparse_masked(
    parser: &mut Parser,
    text: &str,
    tree: &Tree,
) -> Option<(Tree, Vec<(usize, Op)>)> {
    let mut masks = Vec::new();
    collect_operator_selectors(tree.root_node(), text, &mut masks);
    let fields = keyword_fields(text);
    if masks.is_empty() && fields.is_empty() {
        return None;
    }
    let mut masked = text.as_bytes().to_vec();
    let spans = masks.iter().map(|(start, end, _)| (*start, *end));
    for (start, end) in spans.chain(fields.iter().copied()) {
        masked[start..end].fill(b'x');
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
    let names_field = |&(start, end): &(usize, usize)| {
        let node = reparsed.root_node().descendant_for_byte_range(start, end)?;
        let parent = node.parent()?;
        let is_field = node.kind() == "identifier"
            && (node.start_byte(), node.end_byte()) == (start, end)
            && matches!(parent.kind(), "record_literal" | "set_of_records");
        is_field.then_some(())
    };
    let is_repaired = masks.iter().all(|mask| ends_reference(mask).is_some())
        && fields.iter().all(|field| names_field(field).is_some());
    is_repaired.then(|| (reparsed, masks.into_iter().map(|(start, _, op)| (start, op)).collect()))
}

/// The keywords of the grammar that SANY reads as identifiers and that the grammar can't read as
/// the first field of a record: those right after a `[` and followed by `|->` or `:`, outside
/// comments and strings. Their byte ranges.
fn keyword_fields(text: &str) -> Vec<(usize, usize)> {
    const KEYWORDS: &[&str] = &["Nat", "Int", "Real", "STRING", "BOOLEAN", "TRUE", "FALSE"];
    let bytes = text.as_bytes();
    let is_word = |byte: u8| byte.is_ascii_alphanumeric() || byte == b'_';
    let skip_spaces = |mut at: usize| {
        while at < bytes.len() && bytes[at].is_ascii_whitespace() {
            at += 1;
        }
        at
    };
    let mut fields = Vec::new();
    let (mut at, mut depth) = (0, 0);
    while at < bytes.len() {
        let rest = &bytes[at..];
        if rest.starts_with(b"(*") {
            (depth, at) = (depth + 1, at + 2);
        } else if depth > 0 {
            at += if rest.starts_with(b"*)") {
                depth -= 1;
                2
            } else {
                1
            };
        } else if rest.starts_with(b"\\*") {
            at += rest.iter().position(|&byte| byte == b'\n').unwrap_or(rest.len());
        } else if rest[0] == b'"' {
            at += 1;
            while at < bytes.len() && !matches!(bytes[at], b'"' | b'\n') {
                at += if bytes[at] == b'\\' { 2 } else { 1 };
            }
            at += 1;
        } else if rest[0] == b'[' {
            let start = skip_spaces(at + 1);
            let end = start + bytes[start..].iter().take_while(|&&byte| is_word(byte)).count();
            let after = &bytes[skip_spaces(end)..];
            let is_field = after.starts_with(b"|->")
                || (after.starts_with(b":")
                    && !after.starts_with(b"::")
                    && !after.starts_with(b":="));
            if is_field && KEYWORDS.contains(&&text[start..end]) {
                fields.push((start, end));
            }
            at += 1;
        } else {
            at += 1;
        }
    }
    fields
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
