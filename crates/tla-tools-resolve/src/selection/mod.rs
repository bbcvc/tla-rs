//! Subexpression references: names such as `Inv!2`, `Op(a)!lab(b)!<<`, `Op!@`, or `I!Op!:` for
//! part of a definition.
//!
//! A reference resolves to a definition of its own, the selection, made where the referenced
//! definition is: at its depth, in its frames, and in its module's names. The selection's
//! parameters are those of the definition, of the labels, and of the binders on the way to the
//! part, and its body is the part, inside the `LET`s around it. The reference applies the
//! selection to its arguments, or passes it as an operator when it gives none.

mod navigate;

use std::rc::Rc;

use tla_tools_ast::{
    self as ast, Component, Name, OpDecl, Selector, SelectorKind, Span, Symbol, Unit,
};

use self::navigate::{Path, Selected, Step, navigate};
use crate::expr::{FrameScope, apply};
use crate::ir::{DefBody, DefId, Expr, ExprKind, Local, OpRef, Scope};
use crate::module::{Binding, Elab, Entry, InstanceInfo, ParsedModule, SymbolKind};
use crate::{Resolver, Result};

/// Where a module-level definition comes from: its unit in a module's syntax tree, and the
/// elaboration of the module that made it, whose names its body sees.
#[derive(Clone)]
pub(crate) struct Origin {
    pub parsed: Rc<ParsedModule>,
    pub unit: usize,
    pub elab: usize,
}

/// The definition a reference starts from, reached through instances.
struct Target<'s> {
    def: DefId,
    /// How the reference calls it, and so the selection.
    scope: Scope,
    /// The arguments the reference gives it.
    args: &'s [ast::Expr],
    /// The selectors after it.
    rest: &'s [Selector],
}

/// What a reference resolves to.
pub(crate) enum Reference {
    Expr(ExprKind),
    Operator(OpRef),
}

impl Resolver<'_> {
    /// Resolves `M!Op(args)` or `Op(a)!lab(b)`: through instances as a plain operator, or as a
    /// reference to part of a definition. `arity` is the arity of the operator it must be, where
    /// it is an operator argument.
    pub(crate) fn qualified_reference(
        &mut self,
        elab: &Elab,
        path: &[Component],
        name: Name,
        args: &[ast::Expr],
        span: Span,
        arity: Option<usize>,
    ) -> Result<Option<Reference>> {
        if self.is_instance_path(elab, path) {
            return Ok(None);
        }
        let selectors: Vec<Selector> = path
            .iter()
            .map(|component| Selector {
                kind: SelectorKind::Name { name: component.name, args: component.args.clone() },
                span: component.name.span,
            })
            .chain([Selector {
                kind: SelectorKind::Name { name, args: args.to_vec() },
                span: name.span,
            }])
            .collect();
        self.reference(elab, &selectors, span, arity).map(Some)
    }

    /// Whether every component of `path` is a module instance.
    fn is_instance_path(&self, elab: &Elab, path: &[Component]) -> bool {
        let mut current: Option<Rc<InstanceInfo>> = None;
        for component in path {
            let entry = match &current {
                None => self.lookup(elab, component.name.symbol).map(|(entry, _)| entry),
                Some(info) => member(info, component.name.symbol),
            };
            let Some(Entry { binding: Binding::Instance(info), .. }) = entry else { return false };
            current = Some(info);
        }
        true
    }

    /// Resolves a subexpression reference, in an expression, or as an operator of `arity`
    /// arguments.
    pub(crate) fn reference(
        &mut self,
        elab: &Elab,
        selectors: &[Selector],
        span: Span,
        arity: Option<usize>,
    ) -> Result<Reference> {
        let target = self.target(elab, selectors)?;
        let name = self.spec.def(target.def).name;
        let Some(origin) = self.origins.get(&target.def).cloned() else {
            let message = format!("Cannot select a subexpression of {name}.");
            return Err(self.error(elab.module, span, message));
        };
        let (params, body): (&[OpDecl], &ast::Expr) = match &origin.parsed.ast.units[origin.unit] {
            Unit::Operator(definition) => (&definition.params, &definition.body),
            Unit::Assume(assume) => (&[], &assume.expr),
            Unit::Theorem(ast::Theorem { statement: Some(statement), .. }) => (&[], statement),
            _ => {
                let message = format!("Cannot select a subexpression of {name}.");
                return Err(self.error(elab.module, span, message));
            }
        };
        let def_arity = params.len();
        if target.args.len() != def_arity && (arity.is_none() || !target.args.is_empty()) {
            let message = format!("The operator {name} requires {def_arity} arguments.");
            return Err(self.error(elab.module, span, message));
        }
        let path = navigate(params, body, target.args, target.rest, arity.is_some())
            .map_err(|(message, at)| self.error(elab.module, at, message))?;
        let arities = path.arities();
        let text = self.source(elab.module)[span.start as usize..span.end as usize].to_owned();
        let selection = self.select(elab, &origin, target.def, Symbol::intern(&text), &path)?;
        match arity {
            Some(arity) => {
                let is_operator = path.args.is_empty()
                    && arities.len() == arity
                    && arities.iter().all(|&param| param == 0);
                if !is_operator {
                    let message = format!("Expected an operator of {arity} arguments here.");
                    return Err(self.error(elab.module, span, message));
                }
                Ok(Reference::Operator(OpRef::Def { def: selection, scope: target.scope }))
            }
            None => {
                if path.args.len() != arities.len() {
                    let message = format!(
                        "The subexpression requires {} arguments but received {}.",
                        arities.len(),
                        path.args.len()
                    );
                    return Err(self.error(elab.module, span, message));
                }
                let args: Vec<ast::Expr> = path.args.iter().map(|&arg| arg.clone()).collect();
                let args = self.args(elab, &arities, &args)?;
                Ok(Reference::Expr(ExprKind::Call { def: selection, scope: target.scope, args }))
            }
        }
    }

    /// Follows the first names of a reference through instances to a definition.
    fn target<'s>(&mut self, elab: &Elab, selectors: &'s [Selector]) -> Result<Target<'s>> {
        let mut current: Option<(Rc<InstanceInfo>, Scope, usize)> = None;
        for (index, selector) in selectors.iter().enumerate() {
            let SelectorKind::Name { name, args } = &selector.kind else { break };
            let entry = match &current {
                None => self.lookup(elab, name.symbol).map(|(entry, _)| entry),
                Some((info, ..)) => member(info, name.symbol),
            };
            let unknown = || format!("Unknown operator: `{}'.", name.symbol);
            let Some(entry) = entry else {
                return Err(self.error(elab.module, name.span, unknown()));
            };
            match entry.binding {
                Binding::Instance(info) => {
                    if info.params.len() != args.len() {
                        let message = format!(
                            "The operator {} requires {} arguments.",
                            name.symbol,
                            info.params.len()
                        );
                        return Err(self.error(elab.module, name.span, message));
                    }
                    let parent = match &current {
                        None if info.depth == 0 => Scope::Global,
                        None => Scope::Up(self.frames.len() - info.depth),
                        Some((_, scope, defs_depth)) => {
                            self.at_depth(info.depth, *defs_depth, scope)
                        }
                    };
                    let (scope, defs_depth) = if info.params.is_empty() {
                        (parent, info.depth)
                    } else {
                        let args = self.args(elab, &info.params, args)?;
                        (Scope::Instance { parent: Box::new(parent), args }, info.depth + 1)
                    };
                    current = Some((info, scope, defs_depth));
                }
                Binding::Def(def) => {
                    let scope = match &current {
                        None => self.scope_of(def),
                        Some((_, scope, defs_depth)) => {
                            self.at_depth(self.spec.def(def).depth, *defs_depth, scope)
                        }
                    };
                    return Ok(Target { def, scope, args, rest: &selectors[index + 1..] });
                }
                _ => {
                    let message = format!("Cannot select a subexpression of {}.", name.symbol);
                    return Err(self.error(elab.module, name.span, message));
                }
            }
        }
        let span = selectors.first().map(|selector| selector.span).unwrap_or_default();
        Err(self.error(elab.module, span, "A subexpression reference must start with a name."))
    }

    /// Makes the selection: a definition beside `target`, whose body is the selected part.
    fn select(
        &mut self,
        elab: &Elab,
        origin: &Origin,
        target: DefId,
        name: Symbol,
        path: &Path,
    ) -> Result<DefId> {
        let depth = self.spec.def(target).depth;
        // The frames around the target, which its body can't see but its closures capture.
        let mut outer = Vec::new();
        let mut frame = self.layout.defs[target.index()].frame;
        while let Some(id) = frame.and_then(|id| self.layout.frames[id].parent) {
            outer.push(FrameScope { id, ..FrameScope::default() });
            frame = Some(id);
        }
        outer.reverse();
        outer.resize_with(depth, FrameScope::default);
        let frames = std::mem::replace(&mut self.frames, outer);
        let visible_from = std::mem::replace(&mut self.visible_from, depth);
        let at_slots = std::mem::take(&mut self.at_slots);
        let is_instantiating = std::mem::replace(&mut self.is_instantiating, true);
        self.replaying += 1;
        // The body sees the names of the module that made the target, as they are when it was
        // made, unless that elaboration is still going on.
        let owned;
        let target_elab = match self.elab_contexts.get(&origin.elab) {
            Some(context) if origin.elab != elab.id => {
                owned = Elab {
                    id: origin.elab,
                    module: origin.parsed.id,
                    name: origin.parsed.ast.name.symbol,
                    context: (**context).clone(),
                    depth,
                    substitution: None,
                    parsed: origin.parsed.clone(),
                };
                &owned
            }
            _ => elab,
        };
        let name = Name { symbol: name, span: self.spec.def(target).span };
        let def = self.new_def(origin.parsed.id, name, path.arities(), depth);
        self.push_frame(Vec::new());
        let body = self.replay(target_elab, path);
        let frame = self.frames.pop().unwrap();
        let selection = body.map(|body| {
            self.finish_def(def, DefBody::Expr(body), frame);
            def
        });
        self.replaying -= 1;
        self.is_instantiating = is_instantiating;
        self.at_slots = at_slots;
        self.visible_from = visible_from;
        self.frames = frames;
        selection
    }

    /// Resolves the selected part in the selection's frame, after binding the parameters and
    /// `LET` definitions on the way to it.
    fn replay(&mut self, elab: &Elab, path: &Path) -> Result<Expr> {
        for step in &path.steps {
            match step {
                Step::Params(params) => {
                    for &(name, arity) in params {
                        self.bind_replayed(elab, name, arity);
                    }
                }
                Step::Lets(defs) => self.let_defs(elab, defs)?,
            }
        }
        match &path.selected {
            Selected::Expr(expr) => self.expr(elab, expr),
            Selected::LetDef(definition) => {
                let Some((Entry { binding: Binding::Def(def), .. }, _)) =
                    self.lookup(elab, definition.name.symbol)
                else {
                    let message = format!("Unknown operator: `{}'.", definition.name.symbol);
                    return Err(self.error(elab.module, definition.name.span, message));
                };
                let args = definition
                    .params
                    .iter()
                    .map(|param| {
                        let local = Local { hops: 0, slot: self.alloc_slot() };
                        let kind = match param.arity {
                            0 => ExprKind::Local(local),
                            _ => ExprKind::OpArg(OpRef::Param(local)),
                        };
                        Expr::new(kind, definition.name.span)
                    })
                    .collect();
                let scope = self.scope_of(def);
                Ok(Expr::new(apply(OpRef::Def { def, scope }, args), definition.name.span))
            }
        }
    }

    /// Binds a parameter of a selection. The names of the definition's module may include later
    /// ones the parameter would have hidden, which isn't a conflict.
    fn bind_replayed(&mut self, elab: &Elab, name: Name, arity: usize) {
        let slot = self.alloc_slot();
        let entry = Entry {
            binding: Binding::Slot(slot),
            kind: SymbolKind::Parameter,
            arity,
            origin: Some((elab.module, name.span)),
            is_local: true,
        };
        self.frames.last_mut().unwrap().names.push((name.symbol, entry));
    }
}

fn member(info: &InstanceInfo, symbol: Symbol) -> Option<Entry> {
    info.context.names.get(&symbol).filter(|entry| !entry.is_local).cloned()
}
