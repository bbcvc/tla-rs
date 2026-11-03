//! Lowers tree-sitter-tlaplus expression nodes into [`tla_ast::Expr`].

use tla_ast::{
    CaseArm, Component, ExceptKey, ExceptUpdate, Expr, ExprKind, Fairness, Name, Op, Operand,
    Pattern, Quantifier, Selector, SelectorKind, Symbol,
};
use tree_sitter::Node;

use crate::lower::{Lower, Result, children, fields, op_of};

impl Lower<'_> {
    pub fn expr(&self, node: Node) -> Result<Expr> {
        let kind = match node.kind() {
            "parentheses" => return self.only_child(node),
            "label" => ExprKind::Label {
                name: self.name(self.field(node, "name")?)?,
                params: fields(node, "parameter")
                    .into_iter()
                    .map(|param| self.name(param))
                    .collect::<Result<_>>()?,
                body: self.boxed(self.field(node, "expression")?)?,
            },
            "nat_number" => ExprKind::Int(self.int(node, self.text(node), 10)?),
            "binary_number" | "octal_number" | "hex_number" => self.radix_int(node)?,
            "real_number" => return Err(self.unsupported(node, "a real number")),
            "boolean" => ExprKind::Bool(self.text(node) == "TRUE"),
            "string" => ExprKind::Str(Symbol::intern(&unescape(self.text(node)))),
            "prev_func_val" => ExprKind::At,
            "identifier_ref" | "nat_number_set" | "int_number_set" | "real_number_set"
            | "boolean_set" | "string_set" | "infix_op_symbol" | "prefix_op_symbol"
            | "postfix_op_symbol" => ExprKind::Apply { name: self.name(node)?, args: Vec::new() },
            "bound_op" => ExprKind::Apply {
                name: self.name(self.field(node, "name")?)?,
                args: self.exprs(fields(node, "parameter"))?,
            },
            "prefixed_op" | "subexpression" => self.reference(node)?,
            "bound_nonfix_op" => self.nonfix(node)?,
            "bound_infix_op" => self.infix(node)?,
            "bound_prefix_op" => ExprKind::Prefix {
                op: self.op(self.field(node, "symbol")?)?,
                arg: self.boxed(self.field(node, "rhs")?)?,
            },
            "bound_postfix_op" => ExprKind::Postfix {
                op: self.op(self.field(node, "symbol")?)?,
                arg: self.boxed(self.field(node, "lhs")?)?,
            },
            "conj_list" => ExprKind::And(self.junction_items(node)?),
            "disj_list" => ExprKind::Or(self.junction_items(node)?),
            "if_then_else" => ExprKind::If {
                cond: self.boxed(self.field(node, "if")?)?,
                then: self.boxed(self.field(node, "then")?)?,
                otherwise: self.boxed(self.field(node, "else")?)?,
            },
            "case" => self.case(node)?,
            "let_in" => ExprKind::Let {
                defs: fields(node, "definitions")
                    .into_iter()
                    .filter_map(|definition| self.unit(definition, false).transpose())
                    .collect::<Result<_>>()?,
                body: self.boxed(self.field(node, "expression")?)?,
            },
            "bounded_quantification" => ExprKind::Quant {
                quantifier: self.quantifier(self.field(node, "quantifier")?)?,
                bounds: self.bounds(fields(node, "bound"))?,
                body: self.boxed(self.field(node, "expression")?)?,
            },
            "unbounded_quantification" => ExprKind::UnboundedQuant {
                quantifier: self.quantifier(self.field(node, "quantifier")?)?,
                names: fields(node, "intro")
                    .into_iter()
                    .map(|intro| self.name(intro))
                    .collect::<Result<_>>()?,
                body: self.boxed(self.field(node, "expression")?)?,
            },
            "choose" => {
                let intro = self.field(node, "intro")?;
                ExprKind::Choose {
                    pattern: if intro.kind() == "tuple_of_identifiers" {
                        Pattern::Tuple(self.names(intro)?)
                    } else {
                        Pattern::Names(vec![self.name(intro)?])
                    },
                    set: node.child_by_field_name("set").map(|set| self.boxed(set)).transpose()?,
                    body: self.boxed(self.field(node, "expression")?)?,
                }
            }
            "finite_set_literal" => ExprKind::SetEnum(self.exprs(children(node))?),
            "set_filter" => ExprKind::SetFilter {
                bound: Box::new(self.bound(self.field(node, "generator")?)?),
                pred: self.boxed(self.field(node, "filter")?)?,
            },
            "set_map" => ExprKind::SetMap {
                body: self.boxed(self.field(node, "map")?)?,
                bounds: self.bounds(fields(node, "generator"))?,
            },
            "tuple_literal" => ExprKind::Tuple(self.exprs(children(node))?),
            "record_literal" => ExprKind::Record(self.fields_and_values(node)?),
            "set_of_records" => ExprKind::RecordSet(self.fields_and_values(node)?),
            "set_of_functions" => {
                let [domain, range] = self.exact::<2>(node)?;
                ExprKind::FuncSet { domain: self.boxed(domain)?, range: self.boxed(range)? }
            }
            "function_literal" => {
                let (body, bounds) = self.last_and_rest(node)?;
                ExprKind::Function { bounds: self.bounds(bounds)?, body: self.boxed(body)? }
            }
            "function_evaluation" => {
                let parts = children(node);
                let (func, args) =
                    parts.split_first().ok_or_else(|| self.error(node, "empty application"))?;
                ExprKind::FuncApp { func: self.boxed(*func)?, args: self.exprs(args.to_vec())? }
            }
            "record_value" => {
                let [record, field] = self.exact::<2>(node)?;
                ExprKind::Dot { record: self.boxed(record)?, field: self.name(field)? }
            }
            "except" => self.except(node)?,
            "step_expr_or_stutter" => {
                let [action, sub] = self.exact::<2>(node)?;
                ExprKind::BoxAction { action: self.boxed(action)?, sub: self.boxed(sub)? }
            }
            "step_expr_no_stutter" => {
                let [action, sub] = self.exact::<2>(node)?;
                ExprKind::AngleAction { action: self.boxed(action)?, sub: self.boxed(sub)? }
            }
            "fairness" => {
                let [sub, action] = self.exact::<2>(node)?;
                let fairness = match node.child(0).map(|token| self.text(token)) {
                    Some("SF_") => Fairness::Strong,
                    _ => Fairness::Weak,
                };
                ExprKind::Fairness { fairness, sub: self.boxed(sub)?, action: self.boxed(action)? }
            }
            "lambda" => {
                let (body, params) = self.last_and_rest(node)?;
                ExprKind::Lambda {
                    params: params
                        .into_iter()
                        .map(|param| self.name(param))
                        .collect::<Result<_>>()?,
                    body: self.boxed(body)?,
                }
            }
            "proof_step_ref" => return Err(self.unsupported(node, "a proof step reference")),
            kind => return Err(self.unsupported(node, kind)),
        };
        Ok(Expr::new(kind, self.span(node)))
    }

    fn boxed(&self, node: Node) -> Result<Box<Expr>> {
        self.expr(node).map(Box::new)
    }

    fn exprs(&self, nodes: Vec<Node>) -> Result<Vec<Expr>> {
        nodes.into_iter().map(|node| self.expr(node)).collect()
    }

    fn bounds(&self, nodes: Vec<Node>) -> Result<Vec<tla_ast::Bound>> {
        nodes.into_iter().map(|node| self.bound(node)).collect()
    }

    fn only_child(&self, node: Node) -> Result<Expr> {
        let [inner] = self.exact::<1>(node)?;
        self.expr(inner)
    }

    fn exact<'t, const N: usize>(&self, node: Node<'t>) -> Result<[Node<'t>; N]> {
        children(node)
            .try_into()
            .map_err(|_| self.error(node, format!("malformed {}", node.kind())))
    }

    /// Splits the meaningful children into the last one and the ones before it.
    fn last_and_rest<'t>(&self, node: Node<'t>) -> Result<(Node<'t>, Vec<Node<'t>>)> {
        let mut parts = children(node);
        let last = parts.pop().ok_or_else(|| self.error(node, format!("empty {}", node.kind())))?;
        Ok((last, parts))
    }

    fn op(&self, node: Node) -> Result<Op> {
        op_of(node).ok_or_else(|| self.error(node, format!("unknown operator {}", node.kind())))
    }

    fn int(&self, node: Node, digits: &str, radix: u32) -> Result<i64> {
        i64::from_str_radix(digits, radix).map_err(|_| self.error(node, "number is too large"))
    }

    /// `\b101`, `\o17`, or `\h1F`.
    fn radix_int(&self, node: Node) -> Result<ExprKind> {
        let mut format = None;
        let mut value = None;
        let mut cursor = node.walk();
        for child in node.named_children(&mut cursor) {
            match child.kind() {
                "format" => format = Some(self.text(child)),
                "value" => value = Some(self.text(child)),
                _ => {}
            }
        }
        let radix = match format.map(str::to_ascii_lowercase).as_deref() {
            Some("\\b") => 2,
            Some("\\o") => 8,
            Some("\\h") => 16,
            _ => return Err(self.error(node, "unknown number format")),
        };
        let digits = value.ok_or_else(|| self.error(node, "number has no digits"))?;
        Ok(ExprKind::Int(self.int(node, digits, radix)?))
    }

    fn quantifier(&self, node: Node) -> Result<Quantifier> {
        match node.kind() {
            "forall" => Ok(Quantifier::Forall),
            "exists" => Ok(Quantifier::Exists),
            "temporal_forall" => Ok(Quantifier::TemporalForall),
            "temporal_exists" => Ok(Quantifier::TemporalExists),
            kind => Err(self.error(node, format!("unknown quantifier {kind}"))),
        }
    }

    fn infix(&self, node: Node) -> Result<ExprKind> {
        let op = self.op(self.field(node, "symbol")?)?;
        if matches!(op, Op::And | Op::Or | Op::Times) {
            let mut operands = Vec::new();
            self.flatten(node, op, &mut operands)?;
            return Ok(match op {
                Op::And => ExprKind::And(operands),
                Op::Or => ExprKind::Or(operands),
                _ => ExprKind::Product(operands),
            });
        }
        Ok(ExprKind::Infix {
            op,
            lhs: self.boxed(self.field(node, "lhs")?)?,
            rhs: self.boxed(self.field(node, "rhs")?)?,
        })
    }

    /// Collects the operands of a chain of one associative operator, such as `a /\ b /\ c`.
    fn flatten(&self, node: Node, op: Op, operands: &mut Vec<Expr>) -> Result<()> {
        for side in [self.field(node, "lhs")?, self.field(node, "rhs")?] {
            let is_same_op = side.kind() == "bound_infix_op"
                && side.child_by_field_name("symbol").and_then(op_of) == Some(op);
            if is_same_op {
                self.flatten(side, op, operands)?;
            } else {
                operands.push(self.expr(side)?);
            }
        }
        Ok(())
    }

    /// An operator applied in prefix form, such as `\cup(A, B)` after `M!`.
    fn nonfix(&self, node: Node) -> Result<ExprKind> {
        let symbol = self.field(node, "symbol")?;
        let op = self.op(symbol)?;
        let args = children(node).into_iter().filter(|child| child.id() != symbol.id()).collect();
        let mut args = self.exprs(args)?.into_iter();
        let kind = match (symbol.kind(), args.len()) {
            ("infix_op_symbol", 2) => {
                let (lhs, rhs) = (args.next().unwrap(), args.next().unwrap());
                ExprKind::Infix { op, lhs: Box::new(lhs), rhs: Box::new(rhs) }
            }
            ("prefix_op_symbol", 1) => ExprKind::Prefix { op, arg: Box::new(args.next().unwrap()) },
            ("postfix_op_symbol", 1) => {
                ExprKind::Postfix { op, arg: Box::new(args.next().unwrap()) }
            }
            _ => {
                return Err(self.error(node, format!("wrong number of arguments to {}", op.name())));
            }
        };
        Ok(kind)
    }

    /// A name with `!` in it: `M!Op(args)` or `M(x)!N!Op` through instances, or a reference to
    /// part of a definition such as `Op(1)!lab(2)` or `Op!2!<<`. A reference of names only is
    /// [`ExprKind::Qualified`], and resolution tells instances from labels.
    fn reference(&self, node: Node) -> Result<ExprKind> {
        let mut selectors = Vec::new();
        self.selectors(node, &mut selectors)?;
        let is_names =
            selectors.iter().all(|selector| matches!(selector.kind, SelectorKind::Name { .. }));
        if !is_names {
            return Ok(ExprKind::Subexpression(selectors));
        }
        let mut path: Vec<Component> = selectors
            .into_iter()
            .map(|selector| match selector.kind {
                SelectorKind::Name { name, args } => Component { name, args },
                _ => unreachable!("only names"),
            })
            .collect();
        let Component { name, args } = path.pop().expect("a reference has a name after a `!`");
        Ok(ExprKind::Qualified { path, name, args })
    }

    fn selectors(&self, node: Node, selectors: &mut Vec<Selector>) -> Result<()> {
        for child in children(node) {
            let kind = match child.kind() {
                "subexpr_prefix" => {
                    self.selectors(child, selectors)?;
                    continue;
                }
                "subexpr_component" => self.name_selector(self.exact::<1>(child)?[0])?,
                "subexpr_tree_nav" => {
                    // `:`, `<<`, and `>>` are punctuation elsewhere, so take the child as it is.
                    let nav =
                        child.named_child(0).ok_or_else(|| self.error(child, "empty selector"))?;
                    self.navigation(nav)?
                }
                "proof_step_ref" => return Err(self.unsupported(child, "a proof step reference")),
                _ => self.name_selector(child)?,
            };
            selectors.push(Selector { kind, span: self.span(child) });
        }
        Ok(())
    }

    /// `Op`, `Op(a, b)`, `++(a, b)`, or `++` between `!`s.
    fn name_selector(&self, node: Node) -> Result<SelectorKind> {
        let (name, args) = match node.kind() {
            "bound_op" => {
                (self.name(self.field(node, "name")?)?, self.exprs(fields(node, "parameter"))?)
            }
            "bound_nonfix_op" => {
                let symbol = self.field(node, "symbol")?;
                let args =
                    children(node).into_iter().filter(|child| child.id() != symbol.id()).collect();
                (self.name(symbol)?, self.exprs(args)?)
            }
            _ => (self.name(node)?, Vec::new()),
        };
        Ok(SelectorKind::Name { name, args })
    }

    /// `!<<`, `!>>`, `!2`, `!:`, `!@`, or `!(a, b)`.
    fn navigation(&self, node: Node) -> Result<SelectorKind> {
        Ok(match node.kind() {
            "langle_bracket" => SelectorKind::Operand(Operand::First),
            "rangle_bracket" => SelectorKind::Operand(Operand::Second),
            "child_id" => {
                let index =
                    self.text(node).parse().map_err(|_| self.error(node, "operand too large"))?;
                SelectorKind::Operand(Operand::Index(index))
            }
            "colon" => SelectorKind::Colon,
            "address" => SelectorKind::At,
            "operator_args" => SelectorKind::Bound(self.exprs(children(node))?),
            kind => return Err(self.unsupported(node, kind)),
        })
    }

    fn junction_items(&self, node: Node) -> Result<Vec<Expr>> {
        children(node).into_iter().map(|item| self.only_child(item)).collect()
    }

    fn case(&self, node: Node) -> Result<ExprKind> {
        let mut arms = Vec::new();
        let mut other = None;
        for child in children(node) {
            match child.kind() {
                "case_arm" => {
                    let [guard, body] = self.exact::<2>(child)?;
                    arms.push(CaseArm { guard: self.expr(guard)?, body: self.expr(body)? });
                }
                "other_arm" => other = Some(Box::new(self.only_child(child)?)),
                kind => return Err(self.error(child, format!("unexpected {kind} in CASE"))),
            }
        }
        Ok(ExprKind::Case { arms, other })
    }

    /// The `name |-> value` or `name : set` pairs of a record or a set of records.
    fn fields_and_values(&self, node: Node) -> Result<Vec<(Name, Expr)>> {
        children(node)
            .chunks(2)
            .map(|pair| match pair {
                [name, value] => Ok((self.name(*name)?, self.expr(*value)?)),
                _ => Err(self.error(node, format!("malformed {}", node.kind()))),
            })
            .collect()
    }

    fn except(&self, node: Node) -> Result<ExprKind> {
        let base = self.boxed(self.field(node, "expr_to_update")?)?;
        let mut updates = Vec::new();
        for update in children(node).into_iter().filter(|child| child.kind() == "except_update") {
            let mut path = Vec::new();
            for specifier in fields(update, "update_specifier") {
                for key in children(specifier) {
                    path.push(match key.kind() {
                        "except_update_fn_appl" => ExceptKey::Apply(self.exprs(children(key))?),
                        "except_update_record_field" => {
                            let [field] = self.exact::<1>(key)?;
                            ExceptKey::Field(self.name(field)?)
                        }
                        kind => return Err(self.error(key, format!("unexpected {kind} in EXCEPT"))),
                    });
                }
            }
            updates.push(ExceptUpdate { path, value: self.expr(self.field(update, "new_val")?)? });
        }
        Ok(ExprKind::Except { base, updates })
    }
}

/// The value of a string literal, without its quotes and with escapes replaced.
fn unescape(literal: &str) -> String {
    let inner = &literal[1..literal.len() - 1];
    let mut value = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(char) = chars.next() {
        if char != '\\' {
            value.push(char);
            continue;
        }
        match chars.next() {
            Some('n') => value.push('\n'),
            Some('t') => value.push('\t'),
            Some('r') => value.push('\r'),
            Some('f') => value.push('\x0c'),
            Some(other) => value.push(other),
            None => value.push('\\'),
        }
    }
    value
}
