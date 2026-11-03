//! Lowers the tree-sitter-tlaplus concrete syntax tree into [`tla_ast`] modules and units.

use tla_ast::{
    Assume, Bound, FunctionDef, Instance, Module, ModuleDef, Name, Op, OpDecl, OperatorDef,
    Pattern, Span, Substitution, Symbol, Theorem, Unit,
};
use tree_sitter::Node;

use crate::ParseError;

pub(crate) type Result<T> = std::result::Result<T, ParseError>;

/// Named nodes that only mark syntax, such as `==` or a `/\` bullet, and carry no meaning once
/// the tree has its shape.
const PUNCTUATION: &[&str] = &[
    "all_map_to",
    "block_comment",
    "bullet_conj",
    "bullet_disj",
    "case_arrow",
    "case_box",
    "colon",
    "comment",
    "def_eq",
    "double_line",
    "gets",
    "header_line",
    "label_as",
    "langle_bracket",
    "maps_to",
    "rangle_bracket",
    "rangle_bracket_sub",
    "set_in",
    "single_line",
];

pub(crate) struct Lower<'a> {
    /// The source as written. Text and spans always refer to it.
    pub source: &'a str,
    /// The tabs expanded in the text tree-sitter parsed, if the source has any.
    pub tabs: &'a [Tab],
}

/// A tab that [`expand_tabs`] replaced with spaces.
pub(crate) struct Tab {
    expanded: usize,
    original: usize,
    width: usize,
}

/// Replaces each tab with spaces up to the next multiple of 8 columns, as SANY measures columns,
/// so tree-sitter aligns `/\` and `\/` bullets the way SANY does. Returns `None` if there are no
/// tabs.
pub(crate) fn expand_tabs(source: &str) -> Option<(String, Vec<Tab>)> {
    if !source.contains('\t') {
        return None;
    }
    let mut text = String::with_capacity(source.len());
    let mut tabs = Vec::new();
    let mut column = 0;
    for (original, char) in source.char_indices() {
        match char {
            '\t' => {
                let width = 8 - column % 8;
                tabs.push(Tab { expanded: text.len(), original, width });
                text.extend(std::iter::repeat_n(' ', width));
                column += width;
            }
            '\n' => {
                text.push('\n');
                column = 0;
            }
            _ => {
                text.push(char);
                column += 1;
            }
        }
    }
    Some((text, tabs))
}

/// The named children of `node` that carry meaning, in source order.
pub(crate) fn children<'t>(node: Node<'t>) -> Vec<Node<'t>> {
    let mut cursor = node.walk();
    node.named_children(&mut cursor).filter(|child| !PUNCTUATION.contains(&child.kind())).collect()
}

/// The named nodes under field `name`, skipping parentheses and commas.
pub(crate) fn fields<'t>(node: Node<'t>, name: &str) -> Vec<Node<'t>> {
    let mut cursor = node.walk();
    node.children_by_field_name(name, &mut cursor).filter(|child| child.is_named()).collect()
}

/// The operator a symbol node stands for. Accepts both a bare symbol such as `cup` and a wrapper
/// such as `infix_op_symbol`.
pub(crate) fn op_of(node: Node) -> Option<Op> {
    let symbol = if node.kind().ends_with("_op_symbol") { node.named_child(0)? } else { node };
    Op::from_syntax_kind(symbol.kind())
}

fn builtin_set_name(kind: &str) -> Option<&'static str> {
    match kind {
        "nat_number_set" => Some("Nat"),
        "int_number_set" => Some("Int"),
        "real_number_set" => Some("Real"),
        "boolean_set" => Some("BOOLEAN"),
        "string_set" => Some("STRING"),
        _ => None,
    }
}

impl<'a> Lower<'a> {
    /// Maps a byte offset in the parsed text back to the source.
    fn original(&self, offset: usize) -> usize {
        let index = self.tabs.partition_point(|tab| tab.expanded <= offset);
        let Some(tab) = index.checked_sub(1).map(|index| &self.tabs[index]) else {
            return offset;
        };
        if offset < tab.expanded + tab.width {
            tab.original
        } else {
            offset - (tab.expanded + tab.width) + tab.original + 1
        }
    }

    pub fn span(&self, node: Node) -> Span {
        Span::new(self.original(node.start_byte()), self.original(node.end_byte()))
    }

    pub fn text(&self, node: Node) -> &'a str {
        let span = self.span(node);
        &self.source[span.start as usize..span.end as usize]
    }

    pub fn error(&self, node: Node, message: impl Into<String>) -> ParseError {
        ParseError::new(self.source, self.span(node), message)
    }

    pub fn unsupported(&self, node: Node, what: &str) -> ParseError {
        self.error(node, format!("{what} is not supported"))
    }

    pub fn field<'t>(&self, node: Node<'t>, name: &str) -> Result<Node<'t>> {
        node.child_by_field_name(name)
            .ok_or_else(|| self.error(node, format!("{} has no {name}", node.kind())))
    }

    /// The name an identifier, operator symbol, or built-in set node spells.
    pub fn name(&self, node: Node) -> Result<Name> {
        let text = match node.kind() {
            "identifier" | "identifier_ref" => self.text(node),
            _ => match op_of(node) {
                Some(op) => op.name(),
                None => builtin_set_name(node.kind()).ok_or_else(|| {
                    self.error(node, format!("expected a name, found {}", node.kind()))
                })?,
            },
        };
        Ok(Name { symbol: Symbol::intern(text), span: self.span(node) })
    }

    pub fn module(&self, node: Node) -> Result<Module> {
        let name_node = self.field(node, "name")?;
        let mut extends = Vec::new();
        let mut units = Vec::new();
        for child in children(node) {
            if child.id() == name_node.id() {
                continue;
            }
            if child.kind() == "extends" {
                for module in children(child) {
                    extends.push(self.name(module)?);
                }
                continue;
            }
            units.extend(self.unit(child, false)?);
        }
        Ok(Module { name: self.name(name_node)?, extends, units, span: self.span(node) })
    }

    /// Lowers a module unit or `LET` definition. Returns `None` for units TLC ignores, such as
    /// `USE` and `----` separators.
    pub fn unit(&self, node: Node, is_local: bool) -> Result<Option<Unit>> {
        let unit = match node.kind() {
            "variable_declaration" => Unit::Variables(
                children(node).into_iter().map(|child| self.name(child)).collect::<Result<_>>()?,
            ),
            "constant_declaration" => Unit::Constants(self.op_decls(node)?),
            "recursive_declaration" => Unit::Recursive(self.op_decls(node)?),
            "operator_definition" => Unit::Operator(OperatorDef {
                name: self.name(self.field(node, "name")?)?,
                params: self.params(node)?,
                body: self.expr(self.field(node, "definition")?)?,
                is_local,
            }),
            "function_definition" => Unit::Function(FunctionDef {
                name: self.name(self.field(node, "name")?)?,
                bounds: children(node)
                    .into_iter()
                    .filter(|child| child.kind() == "quantifier_bound")
                    .map(|child| self.bound(child))
                    .collect::<Result<_>>()?,
                body: self.expr(self.field(node, "definition")?)?,
                is_local,
            }),
            "instance" => Unit::Instance(self.instance(node, is_local)?),
            "module_definition" => Unit::ModuleDef(ModuleDef {
                name: self.name(self.field(node, "name")?)?,
                params: self.params(node)?,
                instance: self.instance(self.field(node, "definition")?, is_local)?,
                is_local,
            }),
            "local_definition" => {
                let [definition] = children(node)[..] else {
                    return Err(self.error(node, "LOCAL must be followed by one definition"));
                };
                return self.unit(definition, true);
            }
            "assumption" => {
                let name = node.child_by_field_name("name");
                let expr = children(node)
                    .into_iter()
                    .rfind(|child| Some(child.id()) != name.map(|name| name.id()))
                    .ok_or_else(|| self.error(node, "ASSUME has no expression"))?;
                Unit::Assume(Assume {
                    name: name.map(|name| self.name(name)).transpose()?,
                    expr: self.expr(expr)?,
                })
            }
            "theorem" => Unit::Theorem(Theorem {
                name: node.child_by_field_name("name").map(|name| self.name(name)).transpose()?,
                // TLC doesn't check theorems, so a statement that can't be lowered, such as an
                // ASSUME/PROVE, is dropped rather than reported.
                statement: node
                    .child_by_field_name("statement")
                    .and_then(|statement| self.expr(statement).ok()),
                span: self.span(node),
            }),
            "module" => Unit::Module(self.module(node)?),
            "use_or_hide" | "single_line" => return Ok(None),
            kind => return Err(self.unsupported(node, kind)),
        };
        Ok(Some(unit))
    }

    /// The declarations in a `CONSTANT` or `RECURSIVE` list.
    fn op_decls(&self, node: Node) -> Result<Vec<OpDecl>> {
        children(node).into_iter().map(|child| self.op_decl(child)).collect()
    }

    /// `x` (arity 0) or an operator declaration such as `F(_, _)` or `_ ** _`.
    fn op_decl(&self, node: Node) -> Result<OpDecl> {
        if node.kind() != "operator_declaration" {
            return Ok(OpDecl { name: self.name(node)?, arity: 0 });
        }
        let mut cursor = node.walk();
        let arity =
            node.named_children(&mut cursor).filter(|child| child.kind() == "placeholder").count();
        Ok(OpDecl { name: self.name(self.field(node, "name")?)?, arity })
    }

    fn params(&self, node: Node) -> Result<Vec<OpDecl>> {
        fields(node, "parameter").into_iter().map(|param| self.op_decl(param)).collect()
    }

    fn instance(&self, node: Node, is_local: bool) -> Result<Instance> {
        let mut module = None;
        let mut substitutions = Vec::new();
        for child in children(node) {
            if child.kind() != "substitution" {
                module = Some(self.name(child)?);
                continue;
            }
            let [target, value] = children(child)[..] else {
                return Err(self.error(child, "malformed substitution"));
            };
            substitutions.push(Substitution { name: self.name(target)?, value: self.expr(value)? });
        }
        Ok(Instance {
            module: module.ok_or_else(|| self.error(node, "INSTANCE has no module name"))?,
            substitutions,
            is_local,
            span: self.span(node),
        })
    }

    pub fn bound(&self, node: Node) -> Result<Bound> {
        let intros = fields(node, "intro");
        let pattern = match intros[..] {
            [tuple] if tuple.kind() == "tuple_of_identifiers" => Pattern::Tuple(self.names(tuple)?),
            _ => Pattern::Names(
                intros.into_iter().map(|intro| self.name(intro)).collect::<Result<_>>()?,
            ),
        };
        Ok(Bound { pattern, set: self.expr(self.field(node, "set")?)? })
    }

    /// The identifiers inside `<<a, b>>` in a bound or `CHOOSE`.
    pub fn names(&self, tuple: Node) -> Result<Vec<Name>> {
        children(tuple).into_iter().map(|child| self.name(child)).collect()
    }
}
