//! Parses TLA+ modules with tree-sitter-tlaplus and lowers them into [`tla_ast`] trees, and parses
//! TLC model configuration (`.cfg`) files.

mod config;
mod expr;
mod lower;

pub use config::{
    ConfigError, ConfigValue, ConstantAssignment, ConstantSubstitution, ModelConfig, parse_config,
};

use tla_ast::{Module, Span};
use tree_sitter::{Node, Parser};

use crate::lower::{Lower, expand_tabs};

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
    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_tlaplus::LANGUAGE.into())
        .expect("the tree-sitter-tlaplus grammar matches the tree-sitter version");
    let expanded = expand_tabs(source);
    let text = expanded.as_ref().map_or(source, |(text, _)| text.as_str());
    let tree = parser
        .parse(text, None)
        .ok_or_else(|| ParseError::new(source, Span::default(), "the parser gave up"))?;
    let lower = Lower { source, tabs: expanded.as_ref().map_or(&[], |(_, tabs)| tabs.as_slice()) };
    let root = tree.root_node();
    let mut cursor = root.walk();
    let module = root.named_children(&mut cursor).find(|child| child.kind() == "module");
    let module = module.ok_or_else(|| {
        let message = if root.is_error() { "syntax error" } else { "no module found" };
        ParseError::new(source, lower.span(root), message)
    })?;
    if let Some(error) = first_error(module) {
        let message = if error.is_missing() {
            format!("missing {}", error.kind())
        } else {
            "syntax error".to_owned()
        };
        return Err(ParseError::new(source, lower.span(error), message));
    }
    lower.module(module)
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
