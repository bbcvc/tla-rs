//! Finds the part of a definition's syntax tree that the selectors of a subexpression reference
//! name, as SANY's `Generator.selectorToNode` and tla-ts `selectSubexpression` do. On the way it
//! collects what the part depends on: the parameters of the definition, of labels, and of
//! binders, which become parameters of the selection, and the `LET`s around it.

use std::borrow::Cow;

use tla_tools_ast::{
    Bound, Expr, ExprKind, Name, OpDecl, Operand, OperatorDef, Pattern, Selector, SelectorKind,
    Span, Unit,
};

/// A step on the way to the selected part, which the selection replays to resolve it.
#[derive(Debug)]
pub(crate) enum Step<'a> {
    /// Parameters of the definition, a label, or a binder, each with its arity.
    Params(Vec<(Name, usize)>),
    /// The definitions of a `LET` around the part.
    Lets(&'a [Unit]),
}

#[derive(Debug)]
pub(crate) enum Selected<'a> {
    Expr(Cow<'a, Expr>),
    /// A definition of one of the `LET`s, applied to its own parameters.
    LetDef(&'a OperatorDef),
}

/// The selected part of a definition and what it depends on.
#[derive(Debug)]
pub(crate) struct Path<'a, 's> {
    pub steps: Vec<Step<'a>>,
    /// The arguments the reference gives the parameters, in order.
    pub args: Vec<&'s Expr>,
    pub selected: Selected<'a>,
}

impl Path<'_, '_> {
    /// The arity of each parameter of the selection, in order.
    pub fn arities(&self) -> Vec<usize> {
        let mut arities: Vec<usize> = self
            .steps
            .iter()
            .flat_map(|step| match step {
                Step::Params(params) => params.iter().map(|(_, arity)| *arity).collect(),
                Step::Lets(_) => Vec::new(),
            })
            .collect();
        if let Selected::LetDef(definition) = &self.selected {
            arities.extend(definition.params.iter().map(|param| param.arity));
        }
        arities
    }
}

/// A selection error: its message and where SANY reports it.
pub(crate) type Error = (String, Span);

/// A node the selectors walk through. SANY treats the field of `r.f` and the arguments of
/// `f[a, b]` as operands, which the syntax tree doesn't hold as expressions.
#[derive(Clone, Copy, Debug)]
enum Node<'a> {
    Expr(&'a Expr),
    /// The tuple of the arguments of `f[a, b]`.
    Tuple(&'a [Expr], Span),
    /// The field name of `r.field`, a string.
    Field(Name),
}

impl<'a> Node<'a> {
    fn into_expr(self) -> Cow<'a, Expr> {
        match self {
            Node::Expr(expr) => Cow::Borrowed(expr),
            Node::Tuple(items, span) => {
                Cow::Owned(Expr::new(ExprKind::Tuple(items.to_vec()), span))
            }
            Node::Field(name) => Cow::Owned(Expr::new(ExprKind::Str(name.symbol), name.span)),
        }
    }

    fn expr(self) -> Option<&'a Expr> {
        match self {
            Node::Expr(expr) => Some(expr),
            _ => None,
        }
    }
}

/// Walks `selectors` into a definition with parameters `params` and body `body`, which the
/// reference gives the arguments `args`. `is_operator` holds where the reference may stand for an
/// operator, so it may leave out arguments.
pub(crate) fn navigate<'a, 's>(
    params: &'a [OpDecl],
    body: &'a Expr,
    args: &'s [Expr],
    selectors: &'s [Selector],
    is_operator: bool,
) -> Result<Path<'a, 's>, Error> {
    let mut walk = Walk {
        steps: vec![Step::Params(params.iter().map(|param| (param.name, param.arity)).collect())],
        args: args.iter().collect(),
        current: Node::Expr(body),
        selectors,
        index: 0,
        is_operator,
    };
    walk.follow_labels()?;
    while let Some(selector) = walk.selectors.get(walk.index) {
        if let SelectorKind::Name { name, args } = &selector.kind {
            if let Some(definition) = walk.enter_let(*name, args, selector.span)? {
                return Ok(Path { steps: walk.steps, args: walk.args, selected: definition });
            }
            walk.follow_labels()?;
            continue;
        }
        walk.select_operand(selector)?;
        walk.index += 1;
    }
    Ok(Path {
        steps: walk.steps,
        args: walk.args,
        selected: Selected::Expr(walk.current.into_expr()),
    })
}

struct Walk<'a, 's> {
    steps: Vec<Step<'a>>,
    args: Vec<&'s Expr>,
    current: Node<'a>,
    selectors: &'s [Selector],
    index: usize,
    is_operator: bool,
}

impl<'a, 's> Walk<'a, 's> {
    /// Follows the labels the next selectors name.
    fn follow_labels(&mut self) -> Result<(), Error> {
        while let Some(Selector { kind: SelectorKind::Name { name, args }, span }) =
            self.selectors.get(self.index)
        {
            let mut lets = Vec::new();
            let label = self.current.expr().and_then(|expr| find_label(expr, *name, &mut lets));
            let Some((params, body)) = label else {
                return Err((format!("Cannot find label `{}'.", name.symbol), *span));
            };
            if !self.is_operator && args.len() != params.len() {
                let message =
                    format!("Label `{}' used with wrong number of arguments.", name.symbol);
                return Err((message, *span));
            }
            self.steps.extend(lets.into_iter().map(Step::Lets));
            self.steps.push(Step::Params(params.iter().map(|param| (*param, 0)).collect()));
            self.args.extend(args);
            self.current = Node::Expr(body);
            self.index += 1;
        }
        Ok(())
    }

    /// Enters the definition of the `LET` the current part is, which `name` names. Returns it
    /// when it is the last selector.
    fn enter_let(
        &mut self,
        name: Name,
        args: &'s [Expr],
        span: Span,
    ) -> Result<Option<Selected<'a>>, Error> {
        let current = self.current.expr().map(skip_labels);
        let Some(ExprKind::Let { defs, body: _ }) = current.map(|expr| &expr.kind) else {
            return Err(("A name selector here must be from a LET clause.".into(), span));
        };
        self.steps.push(Step::Lets(defs));
        let definition = defs.iter().find_map(|unit| match unit {
            Unit::Operator(definition) if definition.name.symbol == name.symbol => Some(definition),
            _ => None,
        });
        let Some(definition) = definition else {
            return Err((format!("Unknown operator: `{}'.", name.symbol), span));
        };
        let arity = definition.params.len();
        if args.len() != arity && (!self.is_operator || !args.is_empty()) {
            let message = format!("The operator {} requires {arity} arguments.", name.symbol);
            return Err((message, span));
        }
        self.args.extend(args);
        self.index += 1;
        if self.index == self.selectors.len() {
            return Ok(Some(Selected::LetDef(definition)));
        }
        let params = definition.params.iter().map(|param| (param.name, param.arity)).collect();
        self.steps.push(Step::Params(params));
        self.current = Node::Expr(&definition.body);
        Ok(None)
    }

    fn select_operand(&mut self, selector: &'s Selector) -> Result<(), Error> {
        let span = selector.span;
        let current = match self.current {
            Node::Expr(expr) => skip_labels(expr),
            _ => return Err(nonexistent(selector)),
        };
        match (&current.kind, &selector.kind) {
            (_, SelectorKind::Colon) => {}
            (ExprKind::Let { defs, body }, SelectorKind::Operand(operand)) => {
                if operand_index(*operand, 1) != Some(0) {
                    return Err(("A LET/IN expression has only one operand".into(), span));
                }
                self.steps.push(Step::Lets(defs));
                self.current = Node::Expr(body);
            }
            (_, SelectorKind::Bound(_) | SelectorKind::At) => {
                let Some(binder) = binder(current) else {
                    return Err(("Unexpected subexpression selector.".into(), span));
                };
                self.steps
                    .push(Step::Params(binder.names.into_iter().map(|name| (name, 0)).collect()));
                if let SelectorKind::Bound(args) = &selector.kind {
                    self.args.extend(args);
                }
                self.current = Node::Expr(binder.body);
            }
            (ExprKind::Case { arms, other }, SelectorKind::Operand(operand)) => {
                let count = arms.len() + usize::from(other.is_some());
                let arm = operand_index(*operand, count).ok_or_else(|| nonexistent(selector))?;
                self.index += 1;
                let part = match self.selectors.get(self.index) {
                    Some(Selector { kind: SelectorKind::Operand(part), .. }) => *part,
                    _ => {
                        return Err((
                            "A subexpression of CASE must have the form !i!j".into(),
                            span,
                        ));
                    }
                };
                let chosen = match (arms.get(arm), operand_index(part, 2)) {
                    (Some(arm), Some(0)) => Some(&arm.guard),
                    (Some(arm), Some(1)) => Some(&arm.body),
                    (None, Some(1)) => other.as_deref(),
                    _ => None,
                };
                let chosen = chosen.ok_or_else(|| ("Nonexistent CASE operand".to_owned(), span))?;
                self.current = Node::Expr(chosen);
            }
            (_, SelectorKind::Operand(operand)) => {
                let operands = match binder(current) {
                    Some(binder) => binder.sets.into_iter().map(Node::Expr).collect(),
                    None => operands(current),
                };
                let index = operand_index(*operand, operands.len());
                self.current = *index
                    .and_then(|index| operands.get(index))
                    .ok_or_else(|| nonexistent(selector))?;
            }
            (_, SelectorKind::Name { .. }) => unreachable!("names are followed elsewhere"),
        }
        Ok(())
    }
}

fn nonexistent(selector: &Selector) -> Error {
    let position = match selector.kind {
        SelectorKind::Operand(Operand::Index(index)) => index.to_string(),
        SelectorKind::Operand(Operand::First) => "<<".into(),
        SelectorKind::Operand(Operand::Second) => ">>".into(),
        _ => "?".into(),
    };
    (format!("Nonexistent operand specified by `argument selector {position}'."), selector.span)
}

/// The index an operand selector picks among `count` operands.
fn operand_index(operand: Operand, count: usize) -> Option<usize> {
    match operand {
        Operand::Index(index) => (1..=count).contains(&index).then(|| index - 1),
        Operand::First => (count > 0).then_some(0),
        Operand::Second => (count == 2).then_some(1),
    }
}

fn skip_labels(mut expr: &Expr) -> &Expr {
    while let ExprKind::Label { body, .. } = &expr.kind {
        expr = body;
    }
    expr
}

/// The label `name` in `expr`, outside other labels and `LAMBDA`s, with its parameters and body.
/// Adds to `lets` the definitions of the `LET`s around it.
fn find_label<'a>(
    expr: &'a Expr,
    name: Name,
    lets: &mut Vec<&'a [Unit]>,
) -> Option<(&'a [Name], &'a Expr)> {
    match &expr.kind {
        ExprKind::Label { name: label, params, body } => {
            (label.symbol == name.symbol).then_some((params.as_slice(), &**body))
        }
        ExprKind::Lambda { .. } => None,
        ExprKind::Let { defs, body } => {
            lets.push(defs);
            let found = find_label(body, name, lets);
            if found.is_none() {
                lets.pop();
            }
            found
        }
        _ => children(expr).into_iter().find_map(|child| find_label(child, name, lets)),
    }
}

/// The names a binder binds, its body, and the sets it binds them to.
struct Binder<'a> {
    names: Vec<Name>,
    body: &'a Expr,
    sets: Vec<&'a Expr>,
}

fn pattern_names(pattern: &Pattern) -> &[Name] {
    match pattern {
        Pattern::Names(names) | Pattern::Tuple(names) => names,
    }
}

fn bounds_binder<'a>(bounds: &'a [Bound], body: &'a Expr) -> Binder<'a> {
    Binder {
        names: bounds.iter().flat_map(|bound| pattern_names(&bound.pattern)).copied().collect(),
        body,
        sets: bounds.iter().map(|bound| &bound.set).collect(),
    }
}

fn binder(expr: &Expr) -> Option<Binder<'_>> {
    Some(match &expr.kind {
        ExprKind::Quant { bounds, body, .. } | ExprKind::Function { bounds, body } => {
            bounds_binder(bounds, body)
        }
        ExprKind::SetMap { body, bounds } => bounds_binder(bounds, body),
        ExprKind::SetFilter { bound, pred } => bounds_binder(std::slice::from_ref(bound), pred),
        ExprKind::Choose { pattern, set, body } => Binder {
            names: pattern_names(pattern).to_vec(),
            body,
            sets: set.as_deref().into_iter().collect(),
        },
        ExprKind::UnboundedQuant { names, body, .. } | ExprKind::Lambda { params: names, body } => {
            Binder { names: names.clone(), body, sets: Vec::new() }
        }
        _ => return None,
    })
}

/// The operands a selector such as `!2` picks from, as tla-ts `getOperands` lists them.
fn operands(expr: &Expr) -> Vec<Node<'_>> {
    fn exprs(items: &[Expr]) -> Vec<Node<'_>> {
        items.iter().map(Node::Expr).collect()
    }
    match &expr.kind {
        ExprKind::Apply { args, .. } | ExprKind::Qualified { args, .. } => exprs(args),
        ExprKind::Prefix { arg, .. } | ExprKind::Postfix { arg, .. } => vec![Node::Expr(arg)],
        ExprKind::Infix { lhs, rhs, .. } => vec![Node::Expr(lhs), Node::Expr(rhs)],
        ExprKind::And(items)
        | ExprKind::Or(items)
        | ExprKind::Tuple(items)
        | ExprKind::SetEnum(items)
        | ExprKind::Product(items) => exprs(items),
        ExprKind::If { cond, then, otherwise } => {
            vec![Node::Expr(cond), Node::Expr(then), Node::Expr(otherwise)]
        }
        ExprKind::Record(fields) | ExprKind::RecordSet(fields) => {
            fields.iter().map(|(_, value)| Node::Expr(value)).collect()
        }
        ExprKind::FuncApp { func, args } => {
            let argument = match args.as_slice() {
                [arg] => Node::Expr(arg),
                _ => Node::Tuple(args, args_span(args, expr.span)),
            };
            vec![Node::Expr(func), argument]
        }
        ExprKind::Dot { record, field } => vec![Node::Expr(record), Node::Field(*field)],
        ExprKind::BoxAction { action, sub } | ExprKind::AngleAction { action, sub } => {
            vec![Node::Expr(action), Node::Expr(sub)]
        }
        ExprKind::Fairness { sub, action, .. } => vec![Node::Expr(sub), Node::Expr(action)],
        ExprKind::FuncSet { domain, range } => vec![Node::Expr(domain), Node::Expr(range)],
        ExprKind::Except { base, .. } => vec![Node::Expr(base)],
        _ => Vec::new(),
    }
}

fn args_span(args: &[Expr], fallback: Span) -> Span {
    match (args.first(), args.last()) {
        (Some(first), Some(last)) => Span { start: first.span.start, end: last.span.end },
        _ => fallback,
    }
}

/// The subexpressions of an expression, where a label may be.
fn children(expr: &Expr) -> Vec<&Expr> {
    let mut children: Vec<&Expr> = match &expr.kind {
        ExprKind::Case { arms, other } => {
            let mut children: Vec<&Expr> =
                arms.iter().flat_map(|arm| [&arm.guard, &arm.body]).collect();
            children.extend(other.as_deref());
            return children;
        }
        ExprKind::Except { base, updates } => {
            let mut children = vec![&**base];
            children.extend(updates.iter().map(|update| &update.value));
            return children;
        }
        _ => Vec::new(),
    };
    if let Some(binder) = binder(expr) {
        children.extend(binder.sets);
        children.push(binder.body);
        return children;
    }
    operands(expr).into_iter().filter_map(Node::expr).collect()
}
