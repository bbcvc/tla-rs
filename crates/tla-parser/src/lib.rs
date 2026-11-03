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

use crate::lower::{Lower, span};

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
    let tree = parser
        .parse(source, None)
        .ok_or_else(|| ParseError::new(source, Span::default(), "the parser gave up"))?;
    let root = tree.root_node();
    let mut cursor = root.walk();
    let module = root.named_children(&mut cursor).find(|child| child.kind() == "module");
    let module = module.ok_or_else(|| {
        let message = if root.is_error() { "syntax error" } else { "no module found" };
        ParseError::new(source, span(root), message)
    })?;
    if let Some(error) = first_error(module) {
        let message = if error.is_missing() {
            format!("missing {}", error.kind())
        } else {
            "syntax error".to_owned()
        };
        return Err(ParseError::new(source, span(error), message));
    }
    Lower { source }.module(module)
}

fn first_error(node: Node) -> Option<Node> {
    if node.is_error() || node.is_missing() {
        return Some(node);
    }
    if !node.has_error() {
        return None;
    }
    let mut cursor = node.walk();
    node.children(&mut cursor).find_map(first_error)
}
