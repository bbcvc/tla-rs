//! Resolves expressions and the definitions inside them.

use std::rc::Rc;

use tla_tools_ast::{self as ast, Component, Name, Op, Span, Symbol, Unit};

use crate::ir::{
    Bound, Builtin, DefBody, DefId, ExceptKey, ExceptUpdate, Expr, ExprKind, Local, ModuleId,
    OpRef, Pattern, Scope,
};
use crate::levels::join;
use crate::module::{Binding, Elab, Entry, InstanceInfo, SymbolKind};
use crate::selection::Reference;
use crate::{Resolver, Result};

/// What a definition claims of its name.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Claim {
    /// The name is the definition's, to bind.
    New,
    /// The name is taken by another definition, so the definition isn't bound to it.
    Unbound,
    /// The name is taken by something other than a definition, so SANY doesn't bind a
    /// function's bound identifiers in its body either.
    Unnamed,
}

/// The names one frame binds so far and how many slots it uses.
#[derive(Default)]
pub(crate) struct FrameScope {
    /// The frame's index in the level pass's layout.
    pub id: usize,
    pub names: Vec<(Symbol, Entry)>,
    pub slots: usize,
    /// The definitions of the `LET`s resolved in the frame.
    pub lets: Vec<DefId>,
    /// The span of the body of each `LET` resolved in the frame.
    pub let_bodies: Vec<Span>,
    /// The span of the body of each label resolved in the frame.
    pub label_bodies: Vec<Span>,
}

/// The built-in operator an operator symbol stands for, if TLA+ defines it itself.
pub(crate) fn builtin_of(op: Op) -> Option<Builtin> {
    Some(match op {
        Op::And => Builtin::And,
        Op::Or => Builtin::Or,
        Op::Eq => Builtin::Eq,
        Op::Neq => Builtin::Neq,
        Op::Not => Builtin::Not,
        Op::Implies => Builtin::Implies,
        Op::Equiv => Builtin::Equiv,
        Op::In => Builtin::In,
        Op::NotIn => Builtin::NotIn,
        Op::SubsetEq => Builtin::SubsetEq,
        Op::Cup => Builtin::Cup,
        Op::Cap => Builtin::Cap,
        Op::SetMinus => Builtin::SetMinus,
        Op::Powerset => Builtin::Powerset,
        Op::Union => Builtin::Union,
        Op::Domain => Builtin::Domain,
        Op::Prime => Builtin::Prime,
        Op::Unchanged => Builtin::Unchanged,
        Op::Enabled => Builtin::Enabled,
        Op::Always => Builtin::Always,
        Op::Eventually => Builtin::Eventually,
        Op::LeadsTo => Builtin::LeadsTo,
        Op::PlusArrow => Builtin::PlusArrow,
        Op::Cdot => Builtin::Cdot,
        _ => return None,
    })
}

/// The expression that applies an operator reference to arguments.
pub(crate) fn apply(op: OpRef, args: Vec<Expr>) -> ExprKind {
    match op {
        OpRef::Def { def, scope } => ExprKind::Call { def, scope, args },
        OpRef::Param(param) => ExprKind::CallParam { param, args },
        OpRef::Const(id) => ExprKind::CallConst { id, args },
        OpRef::Builtin(op) => ExprKind::Builtin { op, args },
    }
}

fn arity_error(name: impl std::fmt::Display, expected: usize, found: usize) -> String {
    format!("The operator {name} requires {expected} arguments, but is applied to {found}.")
}

impl Resolver<'_> {
    fn depth(&self) -> usize {
        self.frames.len()
    }

    /// The scope a call of `def` from the current depth captures.
    pub(crate) fn scope_of(&self, def: DefId) -> Scope {
        match self.spec.def(def).depth {
            0 => Scope::Global,
            depth => Scope::Up(self.depth() - depth),
        }
    }

    pub(crate) fn alloc_slot(&mut self) -> usize {
        let frame = self.frames.last_mut().expect("expressions are resolved inside a frame");
        frame.slots += 1;
        frame.slots - 1
    }

    fn mark(&self) -> usize {
        self.frames.last().map_or(0, |frame| frame.names.len())
    }

    fn release(&mut self, mark: usize) {
        if let Some(frame) = self.frames.last_mut() {
            frame.names.truncate(mark);
        }
    }

    /// Finds the innermost binding of `symbol` the current code can see, with the index of the
    /// frame that binds it, if a frame does.
    pub(crate) fn lookup(&self, elab: &Elab, symbol: Symbol) -> Option<(Entry, Option<usize>)> {
        for index in (self.visible_from..self.frames.len()).rev() {
            let found = self.frames[index].names.iter().rev().find(|(name, _)| *name == symbol);
            if let Some((_, entry)) = found {
                return Some((entry.clone(), Some(index)));
            }
        }
        elab.context.names.get(&symbol).map(|entry| (entry.clone(), None))
    }

    fn bind_local(
        &mut self,
        elab: &Elab,
        name: Name,
        entry: Entry,
        is_bound_variable: bool,
    ) -> Result<()> {
        let current = self.lookup(elab, name.symbol).map(|(entry, _)| entry);
        // A part of a definition resolved again may hide names defined after it.
        let current = current.filter(|_| self.replaying == 0);
        if self.binds(elab.module, name.symbol, current.as_ref(), &entry, is_bound_variable)? {
            self.frames.last_mut().unwrap().names.push((name.symbol, entry));
        }
        Ok(())
    }

    /// Binds a parameter or bound variable to a new slot of the current frame.
    pub(crate) fn bind_slot(&mut self, elab: &Elab, name: Name, arity: usize) -> Result<usize> {
        let slot = self.alloc_slot();
        let entry = Entry {
            binding: Binding::Slot(slot),
            kind: SymbolKind::Parameter,
            arity,
            origin: Some((elab.module, name.span)),
            location: (elab.module, name.span),
            is_local: true,
        };
        self.bind_local(elab, name, entry, true)?;
        Ok(slot)
    }

    fn bind_def(
        &mut self,
        elab: &Elab,
        name: Name,
        extent: Span,
        arity: usize,
        def: DefId,
    ) -> Result<()> {
        let entry = self.operator_entry(elab.module, name, extent, arity, def, true);
        self.bind_local(elab, name, entry, false)
    }

    /// Claims `name` for an operator or function defined at the current depth: the `RECURSIVE`
    /// declaration awaiting it, or else a new definition. Like SANY's `Generator`, reports a
    /// definition of a name that is already visible, at `extent`, where the definition is, and
    /// goes on. Returns the definition and whether it is a new one with a name of its own to
    /// bind, which a function whose name is taken doesn't have.
    pub(crate) fn claim_def(
        &mut self,
        elab: &Elab,
        name: Name,
        extent: Span,
        params: Vec<usize>,
        is_function: bool,
    ) -> Result<(DefId, Claim)> {
        let depth = self.depth();
        if let Some(def) = self.recursive.remove(&(elab.module, name.symbol, depth)) {
            let declared = self.spec.def(def).params.len();
            if is_function && declared != 0 {
                // SANY leaves the declaration undefined.
                let message = format!(
                    "Function {} has operator arguments in its RECURSIVE declaration.",
                    name.symbol
                );
                self.report_here(elab.module, extent, message)?;
                return Ok((self.new_def(elab.module, name, params, depth), Claim::Unbound));
            }
            if declared != params.len() {
                let message = format!(
                    "Definition of {} has different arity than its RECURSIVE declaration.",
                    name.symbol
                );
                self.report_here(elab.module, extent, message)?;
            }
            self.spec.defs[def.index()].params = params;
            return Ok((def, Claim::New));
        }
        let visible = self.lookup(elab, name.symbol).filter(|_| self.replaying == 0);
        let mut claim = Claim::New;
        if let Some((entry, _)) = visible {
            let is_pending =
                matches!(entry.binding, Binding::Def(def) if self.pending.contains(&def));
            let kind = if is_function { "function" } else { "operator" };
            let message = match entry.kind {
                _ if is_pending => {
                    format!("Recursive {kind} {} defined at wrong LET/IN level.", name.symbol)
                }
                _ if is_function => {
                    format!("Function name `{}' already defined or declared.", name.symbol)
                }
                _ => format!("Operator {} already defined or declared.", name.symbol),
            };
            // SANY goes on to make the definition. It binds an operator's name, which may be
            // another error or a warning, but not a function's, whose bound identifiers it binds
            // in the body only if the name it has is a definition.
            self.report_here(elab.module, extent, message)?;
            let is_def = entry.kind == SymbolKind::Operator
                && matches!(entry.binding, Binding::Def(_))
                && !is_pending;
            claim = match is_def {
                true => Claim::Unbound,
                false => Claim::Unnamed,
            };
        }
        let def = self.new_def(elab.module, name, params, depth);
        self.layout.defs[def.index()].section = self.pending_section(elab.module);
        Ok((def, claim))
    }

    /// Reports an error SANY goes on after, unless resolution is speculative, where it fails.
    fn report_here(&mut self, module: ModuleId, span: Span, message: String) -> Result<()> {
        let error = self.error(module, span, message);
        if self.speculative > 0 {
            return Err(error);
        }
        self.report(module, error, false);
        Ok(())
    }

    /// Resolves an operator definition, at module level or in a `LET`.
    pub(crate) fn operator(&mut self, elab: &Elab, definition: &ast::OperatorDef) -> Result<DefId> {
        let arities = definition.params.iter().map(|param| param.arity).collect();
        let extent = operator_extent(definition);
        let (def, _) = self.claim_def(elab, definition.name, extent, arities, false)?;
        let names = definition.params.iter().map(|param| param.name.symbol).collect();
        self.spec.param_names.insert(def, names);
        self.push_frame(Vec::new());
        let body = definition
            .params
            .iter()
            .try_for_each(|param| self.bind_slot(elab, param.name, param.arity).map(|_| ()))
            .and_then(|()| self.expr(elab, &definition.body));
        let frame = self.frames.pop().unwrap();
        self.finish_def(def, DefBody::Expr(body?), frame);
        Ok(def)
    }

    /// Resolves `f[x \in S] == body` into `def`, which is already bound so the body can recur.
    pub(crate) fn function(
        &mut self,
        elab: &Elab,
        def: DefId,
        definition: &ast::FunctionDef,
        claim: Claim,
    ) -> Result<()> {
        self.push_frame(Vec::new());
        let resolved = self.bounds(elab, &definition.bounds).and_then(|bounds| {
            if claim == Claim::Unnamed {
                self.frames.last_mut().unwrap().names.clear();
            }
            let body = self.expr(elab, &definition.body)?;
            Ok(DefBody::Function { bounds, body })
        });
        let frame = self.frames.pop().unwrap();
        self.finish_def(def, resolved?, frame);
        Ok(())
    }

    fn exprs(&mut self, elab: &Elab, exprs: &[ast::Expr]) -> Result<Vec<Expr>> {
        exprs.iter().map(|expr| self.expr(elab, expr)).collect()
    }

    fn boxed(&mut self, elab: &Elab, expr: &ast::Expr) -> Result<Box<Expr>> {
        self.expr(elab, expr).map(Box::new)
    }

    /// Resolves an expression. SANY goes on after most errors in it, reporting the error and
    /// resolving the rest, so the expression in error becomes a placeholder: the spec isn't
    /// checked once there is an error.
    pub(crate) fn expr(&mut self, elab: &Elab, expr: &ast::Expr) -> Result<Expr> {
        let at = self.checkpoint();
        let resolved = self.resolve_expr(elab, expr);
        self.recover(at, elab.module, resolved, || Expr::new(ExprKind::Bool(false), expr.span))
    }

    fn resolve_expr(&mut self, elab: &Elab, expr: &ast::Expr) -> Result<Expr> {
        use ast::ExprKind as A;
        let span = expr.span;
        let kind = match &expr.kind {
            A::Bool(value) => ExprKind::Bool(*value),
            A::Int(value) => ExprKind::Int(*value),
            A::Str(value) => ExprKind::Str(*value),
            A::Apply { name, args } => return self.apply_name(elab, *name, args, span),
            A::Qualified { path, name, args } => {
                match self.qualified_reference(elab, path, *name, args, span, None)? {
                    Some(Reference::Expr(kind)) => kind,
                    _ => {
                        let mut qualified = String::new();
                        for component in path {
                            qualified.push_str(component.name.symbol.as_str());
                            qualified.push('!');
                        }
                        qualified.push_str(name.symbol.as_str());
                        let qualified = Symbol::intern(&qualified);
                        self.spec.qualified_names.insert((elab.module, span), qualified);
                        self.qualified(elab, path, *name, args)?
                    }
                }
            }
            A::Subexpression(selectors) => match self.reference(elab, selectors, span, None)? {
                Reference::Expr(kind) => kind,
                Reference::Operator(op) => ExprKind::OpArg(op),
            },
            A::Label { body, .. } => {
                let body = self.expr(elab, body)?;
                if let Some(frame) = self.frames.last_mut() {
                    frame.label_bodies.push(body.span);
                }
                return Ok(body);
            }
            A::Lambda { .. } => {
                return Err(self.error(
                    elab.module,
                    span,
                    "A LAMBDA expression can only be an argument of an operator.",
                ));
            }
            A::Prefix { op, arg } => match builtin_of(*op) {
                Some(builtin) => {
                    ExprKind::Builtin { op: builtin, args: vec![self.expr(elab, arg)?] }
                }
                None => {
                    let token = Span::new(span.start as usize, arg.span.start as usize);
                    let args = std::slice::from_ref(arg.as_ref());
                    return self.apply_op(elab, *op, args, span, (token, "prefix"));
                }
            },
            A::Postfix { op, arg } => match builtin_of(*op) {
                Some(builtin) => {
                    ExprKind::Builtin { op: builtin, args: vec![self.expr(elab, arg)?] }
                }
                None => {
                    let token = Span::new(arg.span.end as usize, span.end as usize);
                    let args = std::slice::from_ref(arg.as_ref());
                    return self.apply_op(elab, *op, args, span, (token, "postfix"));
                }
            },
            A::Infix { op, lhs, rhs } => match builtin_of(*op) {
                Some(builtin) => ExprKind::Builtin {
                    op: builtin,
                    args: vec![self.expr(elab, lhs)?, self.expr(elab, rhs)?],
                },
                None => {
                    let token = Span::new(lhs.span.end as usize, rhs.span.start as usize);
                    let args = [(**lhs).clone(), (**rhs).clone()];
                    return self.apply_op(elab, *op, &args, span, (token, "infix"));
                }
            },
            A::And(items) => ExprKind::And(self.exprs(elab, items)?),
            A::Or(items) => ExprKind::Or(self.exprs(elab, items)?),
            A::If { cond, then, otherwise } => ExprKind::If {
                cond: self.boxed(elab, cond)?,
                then: self.boxed(elab, then)?,
                otherwise: self.boxed(elab, otherwise)?,
            },
            A::Case { arms, other } => ExprKind::Case {
                arms: arms
                    .iter()
                    .map(|arm| Ok((self.expr(elab, &arm.guard)?, self.expr(elab, &arm.body)?)))
                    .collect::<Result<_>>()?,
                other: other.as_ref().map(|other| self.boxed(elab, other)).transpose()?,
            },
            A::Let { defs, body } => return self.let_in(elab, defs, body),
            A::Quant { quantifier, bounds, body } => {
                let mark = self.mark();
                let resolved = self
                    .bounds(elab, bounds)
                    .and_then(|bounds| Ok((bounds, self.boxed(elab, body)?)));
                self.release(mark);
                let (bounds, body) = resolved?;
                ExprKind::Quant { quantifier: *quantifier, bounds, body }
            }
            A::UnboundedQuant { quantifier, names, body } => {
                let mark = self.mark();
                let resolved = names
                    .iter()
                    .map(|name| self.bind_slot(elab, *name, 0))
                    .collect::<Result<Vec<_>>>()
                    .and_then(|slots| Ok((slots, self.boxed(elab, body)?)));
                self.release(mark);
                let (slots, body) = resolved?;
                ExprKind::UnboundedQuant { quantifier: *quantifier, slots, body }
            }
            A::Choose { pattern, set, body } => {
                let set = set.as_ref().map(|set| self.boxed(elab, set)).transpose()?;
                let mark = self.mark();
                let resolved = self
                    .pattern(elab, pattern)
                    .and_then(|pattern| Ok((pattern, self.boxed(elab, body)?)));
                self.release(mark);
                let (pattern, body) = resolved?;
                ExprKind::Choose { pattern, set, body }
            }
            A::SetEnum(items) => ExprKind::SetEnum(self.exprs(elab, items)?),
            A::SetFilter { bound, pred } => {
                let mark = self.mark();
                let resolved = self
                    .bounds(elab, std::slice::from_ref(bound.as_ref()))
                    .and_then(|mut bounds| Ok((bounds.remove(0), self.boxed(elab, pred)?)));
                self.release(mark);
                let (bound, pred) = resolved?;
                ExprKind::SetFilter { bound: Box::new(bound), pred }
            }
            A::SetMap { body, bounds } => {
                let mark = self.mark();
                let resolved = self
                    .bounds(elab, bounds)
                    .and_then(|bounds| Ok((bounds, self.boxed(elab, body)?)));
                self.release(mark);
                let (bounds, body) = resolved?;
                ExprKind::SetMap { body, bounds }
            }
            A::Function { bounds, body } => {
                let mark = self.mark();
                let resolved = self
                    .bounds(elab, bounds)
                    .and_then(|bounds| Ok((bounds, self.boxed(elab, body)?)));
                self.release(mark);
                let (bounds, body) = resolved?;
                ExprKind::Function { bounds, body }
            }
            A::Tuple(items) => ExprKind::Tuple(self.exprs(elab, items)?),
            A::Record(fields) => ExprKind::Record(self.fields(elab, fields)?),
            A::RecordSet(fields) => ExprKind::RecordSet(self.fields(elab, fields)?),
            A::FuncSet { domain, range } => ExprKind::FuncSet {
                domain: self.boxed(elab, domain)?,
                range: self.boxed(elab, range)?,
            },
            A::FuncApp { func, args } => {
                ExprKind::FuncApp { func: self.boxed(elab, func)?, args: self.exprs(elab, args)? }
            }
            A::Dot { record, field } => {
                ExprKind::Dot { record: self.boxed(elab, record)?, field: field.symbol }
            }
            A::Except { base, updates } => self.except(elab, base, updates)?,
            A::At => {
                let Some(&(depth, slot)) = self.at_slots.last() else {
                    return Err(self.error(
                        elab.module,
                        span,
                        "@ can only appear in the new value of an EXCEPT.",
                    ));
                };
                ExprKind::Local(Local { hops: self.depth() - depth, slot })
            }
            A::Product(factors) => ExprKind::Product(self.exprs(elab, factors)?),
            A::BoxAction { action, sub } => ExprKind::BoxAction {
                action: self.boxed(elab, action)?,
                sub: self.boxed(elab, sub)?,
            },
            A::AngleAction { action, sub } => ExprKind::AngleAction {
                action: self.boxed(elab, action)?,
                sub: self.boxed(elab, sub)?,
            },
            A::Fairness { fairness, sub, action } => ExprKind::Fairness {
                fairness: *fairness,
                sub: self.boxed(elab, sub)?,
                action: self.boxed(elab, action)?,
            },
        };
        Ok(Expr::new(kind, span))
    }

    fn fields(&mut self, elab: &Elab, fields: &[(Name, ast::Expr)]) -> Result<Vec<(Symbol, Expr)>> {
        for (index, (name, _)) in fields.iter().enumerate() {
            if fields[..index].iter().any(|(earlier, _)| earlier.symbol == name.symbol) {
                return Err(self.error(
                    elab.module,
                    name.span,
                    "Non-unique fields in constructor.",
                ));
            }
        }
        fields.iter().map(|(name, value)| Ok((name.symbol, self.expr(elab, value)?))).collect()
    }

    /// Resolves the sets of the bounds, then binds their names, which the sets can't see. The
    /// caller releases the names.
    fn bounds(&mut self, elab: &Elab, bounds: &[ast::Bound]) -> Result<Vec<Bound>> {
        let sets =
            bounds.iter().map(|bound| self.expr(elab, &bound.set)).collect::<Result<Vec<_>>>()?;
        bounds
            .iter()
            .zip(sets)
            .map(|(bound, set)| Ok(Bound { pattern: self.pattern(elab, &bound.pattern)?, set }))
            .collect()
    }

    fn pattern(&mut self, elab: &Elab, pattern: &ast::Pattern) -> Result<Pattern> {
        let (names, is_tuple) = match pattern {
            ast::Pattern::Names(names) => (names, false),
            ast::Pattern::Tuple(names) => (names, true),
        };
        let slots =
            names.iter().map(|name| self.bind_slot(elab, *name, 0)).collect::<Result<Vec<_>>>()?;
        Ok(if is_tuple { Pattern::Tuple(slots) } else { Pattern::Names(slots) })
    }

    fn except(
        &mut self,
        elab: &Elab,
        base: &ast::Expr,
        updates: &[ast::ExceptUpdate],
    ) -> Result<ExprKind> {
        let base = self.boxed(elab, base)?;
        let mut resolved = Vec::new();
        for update in updates {
            let path = update
                .path
                .iter()
                .map(|key| match key {
                    ast::ExceptKey::Apply(args) => Ok(ExceptKey::Apply(self.exprs(elab, args)?)),
                    ast::ExceptKey::Field(name) => Ok(ExceptKey::Field(name.symbol)),
                })
                .collect::<Result<_>>()?;
            let at = self.alloc_slot();
            self.at_slots.push((self.depth(), at));
            let value = self.expr(elab, &update.value);
            self.at_slots.pop();
            resolved.push(ExceptUpdate { path, at, value: value? });
        }
        Ok(ExprKind::Except { base, updates: resolved })
    }

    fn let_in(&mut self, elab: &Elab, defs: &[Unit], body: &ast::Expr) -> Result<Expr> {
        let mark = self.mark();
        let resolved = self.let_defs(elab, defs).and_then(|()| self.expr(elab, body));
        self.release(mark);
        if let (Ok(body), Some(frame)) = (&resolved, self.frames.last_mut()) {
            frame.let_bodies.push(body.span);
        }
        resolved
    }

    pub(crate) fn let_defs(&mut self, elab: &Elab, defs: &[Unit]) -> Result<()> {
        for unit in defs {
            match unit {
                Unit::Recursive(decls) => {
                    for decl in decls {
                        let def = self.declare_recursive(elab.module, decl, self.depth());
                        let extent = self.declaration_extent(elab.module, decl.name.span);
                        self.bind_def(elab, decl.name, extent, decl.arity, def)?;
                    }
                }
                Unit::Operator(definition) => {
                    let def = self.operator(elab, definition)?;
                    let extent = operator_extent(definition);
                    self.bind_def(elab, definition.name, extent, definition.params.len(), def)?;
                    self.frames.last_mut().unwrap().lets.push(def);
                }
                Unit::Function(definition) => {
                    let extent = function_extent(definition);
                    let (def, claim) =
                        self.claim_def(elab, definition.name, extent, Vec::new(), true)?;
                    if claim == Claim::New {
                        self.bind_def(elab, definition.name, extent, 0, def)?;
                    }
                    self.function(elab, def, definition, claim)?;
                    self.frames.last_mut().unwrap().lets.push(def);
                }
                Unit::ModuleDef(definition) => {
                    let info = self.named_instance(elab, definition)?;
                    let entry = Entry {
                        binding: Binding::Instance(info),
                        kind: SymbolKind::Module,
                        arity: definition.params.len(),
                        origin: Some((elab.module, definition.name.span)),
                        location: (
                            elab.module,
                            join(definition.name.span, definition.instance.span),
                        ),
                        is_local: true,
                    };
                    self.bind_local(elab, definition.name, entry, false)?;
                }
                _ => {
                    return Err(self.error(
                        elab.module,
                        body_span(unit),
                        "This kind of unit can't appear in a LET.",
                    ));
                }
            }
        }
        Ok(())
    }

    /// Resolves the arguments of an operator with parameters of the given arities. A parameter
    /// with arity takes an operator.
    pub(crate) fn args(
        &mut self,
        elab: &Elab,
        arities: &[usize],
        args: &[ast::Expr],
    ) -> Result<Vec<Expr>> {
        arities
            .iter()
            .zip(args)
            .map(|(&arity, arg)| match arity {
                0 => self.expr(elab, arg),
                _ => Ok(Expr::new(ExprKind::OpArg(self.op_arg(elab, arg, arity)?), arg.span)),
            })
            .collect()
    }

    /// Applies an operator written as a symbol, between `gap`, the text from its operand to the
    /// other operand or the end, which holds its token. SANY reports a symbol nothing defines
    /// by its token, as it is spelled, and then the application.
    fn apply_op(
        &mut self,
        elab: &Elab,
        op: Op,
        args: &[ast::Expr],
        span: tla_tools_ast::Span,
        (gap, fixity): (Span, &str),
    ) -> Result<Expr> {
        let symbol = Symbol::intern(op.name());
        if self.lookup(elab, symbol).is_none() {
            // SANY reports an operator applied like a function, as `op(a, b)`, as unknown.
            let first = args.first().map_or(span, |arg| arg.span);
            let before = Span::new(span.start as usize, first.start as usize);
            let source = self.source(elab.module);
            let text = &source[before.start as usize..before.end as usize];
            let head = text.trim_end().strip_suffix('(').map(str::trim_end);
            let head = head.filter(|_| fixity != "prefix");
            if let Some(head) = head.filter(|head| !head.trim_start_matches('(').is_empty()) {
                let token = Span::new(span.start as usize, span.start as usize + head.len());
                let message = format!("Unknown operator: `{head}'.");
                return Err(self.error(elab.module, token, message));
            }
            let token = self.token_in(elab.module, gap);
            let source = self.source(elab.module);
            let text = &source[token.start as usize..token.end as usize];
            let text = if fixity == "prefix" && text == "-" { "-." } else { text };
            let message = format!("Could not find declaration or definition of symbol '{text}'.");
            let error = self.error(elab.module, token, message);
            if self.speculative > 0 {
                return Err(error);
            }
            self.report(elab.module, error, false);
            let message = format!("Couldn't resolve {fixity} operator symbol `{text}'.");
            return Err(self.error(elab.module, span, message));
        }
        self.apply_name(elab, Name { symbol, span }, args, span)
    }

    fn apply_name(
        &mut self,
        elab: &Elab,
        name: Name,
        args: &[ast::Expr],
        span: tla_tools_ast::Span,
    ) -> Result<Expr> {
        let Some((entry, frame)) = self.lookup(elab, name.symbol) else {
            return Err(self.error(
                elab.module,
                name.span,
                format!("Unknown operator: `{}'.", name.symbol),
            ));
        };
        // A variable of the module an instance substitutes into, replaced here.
        if entry.kind == SymbolKind::Variable
            && matches!(entry.binding, Binding::Inline(_) | Binding::Def(_))
            && args.is_empty()
        {
            self.spec.instance_variables.insert((elab.module, span), name.symbol);
        }
        let check_arity = |resolver: &Self, expected: usize| {
            if expected == args.len() {
                return Ok(());
            }
            Err(resolver.error(
                elab.module,
                name.span,
                arity_error(name.symbol, expected, args.len()),
            ))
        };
        let kind = match entry.binding {
            Binding::Slot(slot) => {
                let param = Local { hops: self.depth() - frame.unwrap() - 1, slot };
                check_arity(self, entry.arity)?;
                match entry.arity {
                    0 => ExprKind::Local(param),
                    _ => ExprKind::CallParam { param, args: self.exprs(elab, args)? },
                }
            }
            Binding::Var(id) => {
                check_arity(self, 0)?;
                ExprKind::Var(id)
            }
            Binding::Const(id) => {
                check_arity(self, entry.arity)?;
                match entry.arity {
                    0 => ExprKind::Const(id),
                    _ => ExprKind::CallConst { id, args: self.exprs(elab, args)? },
                }
            }
            Binding::Def(def) => {
                let arities = self.spec.def(def).params.clone();
                check_arity(self, arities.len())?;
                ExprKind::Call {
                    def,
                    scope: self.scope_of(def),
                    args: self.args(elab, &arities, args)?,
                }
            }
            Binding::Inline(expr) => {
                check_arity(self, 0)?;
                return Ok(Expr::new(expr.kind.clone(), span));
            }
            Binding::Builtin(op) => {
                check_arity(self, op.arity())?;
                ExprKind::Builtin { op, args: self.exprs(elab, args)? }
            }
            Binding::Instance(_) => {
                return Err(self.error(
                    elab.module,
                    name.span,
                    format!("{} is a module instance, not an operator.", name.symbol),
                ));
            }
        };
        Ok(Expr::new(kind, span))
    }

    /// Resolves an argument for a parameter that takes an operator of `arity` arguments.
    pub(crate) fn op_arg(&mut self, elab: &Elab, arg: &ast::Expr, arity: usize) -> Result<OpRef> {
        let mismatch = |resolver: &Self| {
            resolver.error(
                elab.module,
                arg.span,
                format!("Expected an operator of {arity} arguments here."),
            )
        };
        match &arg.kind {
            ast::ExprKind::Lambda { params, body } => {
                if params.len() != arity {
                    return Err(mismatch(self));
                }
                let depth = self.depth();
                let name = Name { symbol: Symbol::intern("LAMBDA"), span: arg.span };
                let def = self.new_def(elab.module, name, vec![0; arity], depth);
                self.push_frame(Vec::new());
                let body = params
                    .iter()
                    .try_for_each(|param| self.bind_slot(elab, *param, 0).map(|_| ()))
                    .and_then(|()| self.expr(elab, body));
                let frame = self.frames.pop().unwrap();
                self.finish_def(def, DefBody::Expr(body?), frame);
                Ok(OpRef::Def { def, scope: Scope::Up(0) })
            }
            ast::ExprKind::Apply { name, args } if args.is_empty() => {
                let Some((entry, frame)) = self.lookup(elab, name.symbol) else {
                    return Err(self.error(
                        elab.module,
                        name.span,
                        format!("Unknown operator: `{}'.", name.symbol),
                    ));
                };
                if entry.arity != arity {
                    return Err(mismatch(self));
                }
                match entry.binding {
                    Binding::Slot(slot) => {
                        Ok(OpRef::Param(Local { hops: self.depth() - frame.unwrap() - 1, slot }))
                    }
                    // TLA+ is second order: an operator argument takes no operators itself.
                    Binding::Def(def)
                        if self.spec.def(def).params.iter().all(|&arity| arity == 0) =>
                    {
                        Ok(OpRef::Def { def, scope: self.scope_of(def) })
                    }
                    Binding::Const(id) => Ok(OpRef::Const(id)),
                    Binding::Builtin(op) => Ok(OpRef::Builtin(op)),
                    _ => Err(mismatch(self)),
                }
            }
            ast::ExprKind::Subexpression(selectors) => {
                match self.reference(elab, selectors, arg.span, Some(arity))? {
                    Reference::Operator(op) => Ok(op),
                    Reference::Expr(_) => Err(mismatch(self)),
                }
            }
            ast::ExprKind::Qualified { path, name, args } if args.is_empty() => {
                let reference =
                    self.qualified_reference(elab, path, *name, args, arg.span, Some(arity))?;
                if let Some(reference) = reference {
                    return match reference {
                        Reference::Operator(op) => Ok(op),
                        Reference::Expr(_) => Err(mismatch(self)),
                    };
                }
                let (info, scope, defs_depth) = self.instance_path(elab, path)?;
                match self.member(elab, &info, *name)?.binding {
                    Binding::Def(def) if self.spec.def(def).params.len() == arity => {
                        Ok(OpRef::Def { def, scope: self.member_scope(def, defs_depth, scope) })
                    }
                    _ => Err(mismatch(self)),
                }
            }
            _ => Err(mismatch(self)),
        }
    }

    /// Follows `I(args)!J!...` to the last instance. Returns it with the scope its definitions
    /// capture and the depth they are defined at.
    fn instance_path(
        &mut self,
        elab: &Elab,
        path: &[Component],
    ) -> Result<(Rc<InstanceInfo>, Scope, usize)> {
        let mut current: Option<(Rc<InstanceInfo>, Scope, usize)> = None;
        for component in path {
            let entry = match &current {
                None => self.lookup(elab, component.name.symbol).map(|(entry, _)| entry),
                Some((info, ..)) => info
                    .context
                    .names
                    .get(&component.name.symbol)
                    .filter(|entry| !entry.is_local)
                    .cloned(),
            };
            let Some(Entry { binding: Binding::Instance(info), .. }) = entry else {
                return Err(self.error(
                    elab.module,
                    component.name.span,
                    format!("{} is not a module instance.", component.name.symbol),
                ));
            };
            if info.params.len() != component.args.len() {
                return Err(self.error(
                    elab.module,
                    component.name.span,
                    arity_error(component.name.symbol, info.params.len(), component.args.len()),
                ));
            }
            let parent = match &current {
                None if info.depth == 0 => Scope::Global,
                None => Scope::Up(self.depth() - info.depth),
                Some((_, scope, defs_depth)) => self.at_depth(info.depth, *defs_depth, scope),
            };
            let (scope, defs_depth) = if info.params.is_empty() {
                (parent, info.depth)
            } else {
                let args = self.args(elab, &info.params, &component.args)?;
                (Scope::Instance { parent: Box::new(parent), args }, info.depth + 1)
            };
            current = Some((info, scope, defs_depth));
        }
        Ok(current.expect("a qualified name has at least one instance"))
    }

    /// The scope of something defined at `depth` inside an instance whose definitions are at
    /// `defs_depth` and capture `scope`. Definitions an instance shares with plain modules, such
    /// as the standard modules, are global.
    pub(crate) fn at_depth(&self, depth: usize, defs_depth: usize, scope: &Scope) -> Scope {
        if depth == 0 {
            return Scope::Global;
        }
        debug_assert_eq!(depth, defs_depth, "instance definitions live at the instance's depth");
        scope.clone()
    }

    fn member_scope(&self, def: DefId, defs_depth: usize, scope: Scope) -> Scope {
        self.at_depth(self.spec.def(def).depth, defs_depth, &scope)
    }

    fn member(&self, elab: &Elab, info: &InstanceInfo, name: Name) -> Result<Entry> {
        info.context.names.get(&name.symbol).filter(|entry| !entry.is_local).cloned().ok_or_else(
            || self.error(elab.module, name.span, format!("Unknown operator: `{}'.", name.symbol)),
        )
    }

    fn qualified(
        &mut self,
        elab: &Elab,
        path: &[Component],
        name: Name,
        args: &[ast::Expr],
    ) -> Result<ExprKind> {
        let (info, scope, defs_depth) = self.instance_path(elab, path)?;
        // SANY names an operator an instance lacks by the whole reference, `I!Op`.
        let Some(entry) =
            info.context.names.get(&name.symbol).filter(|entry| !entry.is_local).cloned()
        else {
            let mut qualified = String::new();
            for component in path {
                qualified.push_str(&format!("{}!", component.name.symbol));
            }
            let span = join(path.first().map_or(name.span, |first| first.name.span), name.span);
            let message = format!("Unknown operator: `{qualified}{}'.", name.symbol);
            return Err(self.error(elab.module, span, message));
        };
        let expected = match &entry.binding {
            Binding::Def(def) => self.spec.def(*def).params.len(),
            _ => entry.arity,
        };
        if expected != args.len() {
            return Err(self.error(
                elab.module,
                name.span,
                arity_error(name.symbol, expected, args.len()),
            ));
        }
        Ok(match entry.binding {
            Binding::Def(def) => {
                let arities = self.spec.def(def).params.clone();
                ExprKind::Call {
                    def,
                    scope: self.member_scope(def, defs_depth, scope),
                    args: self.args(elab, &arities, args)?,
                }
            }
            Binding::Inline(expr) => expr.kind.clone(),
            Binding::Var(id) => ExprKind::Var(id),
            Binding::Const(id) => ExprKind::Const(id),
            Binding::Builtin(op) => ExprKind::Builtin { op, args: self.exprs(elab, args)? },
            Binding::Slot(_) | Binding::Instance(_) => {
                return Err(self.error(
                    elab.module,
                    name.span,
                    format!("{} is not an operator of the instance.", name.symbol),
                ));
            }
        })
    }
}

fn body_span(unit: &Unit) -> tla_tools_ast::Span {
    match unit {
        Unit::Instance(instance) => instance.span,
        Unit::Assume(assume) => assume.expr.span,
        Unit::Theorem(theorem) => theorem.span,
        Unit::Module(module) => module.span,
        Unit::Hide(hide) => hide.span,
        Unit::Variables(names) => names.first().map(|name| name.span).unwrap_or_default(),
        Unit::Constants(decls) => decls.first().map(|decl| decl.name.span).unwrap_or_default(),
        _ => tla_tools_ast::Span::default(),
    }
}

/// Where an operator definition is: from its name to the end of its body.
pub(crate) fn operator_extent(definition: &ast::OperatorDef) -> Span {
    Span::new(definition.name.span.start as usize, definition.body.span.end as usize)
}

/// Where a function definition is: from its name to the end of its body.
pub(crate) fn function_extent(definition: &ast::FunctionDef) -> Span {
    Span::new(definition.name.span.start as usize, definition.body.span.end as usize)
}
