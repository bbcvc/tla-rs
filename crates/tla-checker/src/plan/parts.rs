//! The parts of a formula: its conjuncts, through the definitions it applies, each made a
//! zero-arity module-level definition the model checker evaluates.

use tla_ast::{Quantifier, Span};
use tla_resolve::{Builtin, Def, DefBody, DefId, DefLevels, Expr, ExprKind, Level, Scope, Spec};
use tla_value::Symbol;

use super::Planner;
use crate::Error;

/// One conjunct of a formula, in the definition whose frame its expression lives in.
pub(super) struct Part {
    pub owner: DefId,
    pub expr: Expr,
    pub name: String,
    /// How a module-level definition reaches the frame of `owner`, when `owner` is a
    /// definition of a parameterized instance.
    pub via: Option<Via>,
}

/// A call of a definition of a parameterized instance, as in `I(y)!Spec`, from a module-level
/// definition.
#[derive(Clone)]
pub(super) struct Via {
    /// The module-level definition the instance's arguments are written in.
    caller: DefId,
    scope: Scope,
}

impl Planner<'_> {
    pub(super) fn body(spec: &Spec, def: DefId) -> Expr {
        match &spec.def(def).body {
            DefBody::Expr(expr) => expr.clone(),
            DefBody::Function { .. } => Expr::new(
                ExprKind::Call { def, scope: Scope::Global, args: Vec::new() },
                spec.def(def).span,
            ),
        }
    }

    /// Splits a formula into its conjuncts, following the zero-arity definitions it applies
    /// that aren't constants, as TLC's `Tool.processSpec` does, those of parameterized
    /// instances included.
    pub(super) fn expand(
        &self,
        part: Part,
        parts: &mut Vec<Part>,
        expanding: &mut Vec<DefId>,
    ) -> Result<(), Error> {
        let Part { owner, expr, name, via } = part;
        // The definition the conjunct applies, and how its frame is reached.
        let (target, inner) = match &expr.kind {
            ExprKind::And(items) => {
                for item in items {
                    let name = self.describe(owner, item.span);
                    let part = Part { owner, expr: item.clone(), name, via: via.clone() };
                    self.expand(part, parts, expanding)?;
                }
                return Ok(());
            }
            ExprKind::Call { def, scope: Scope::Global, args } if args.is_empty() => {
                (*self.overrides.get(def).unwrap_or(def), None)
            }
            // A definition of the parameterized instance `owner` belongs to, in its frame.
            ExprKind::Call { def, scope: Scope::Up(_), args }
                if args.is_empty()
                    && via.is_some()
                    && self.spec.def(*def).depth == self.spec.def(owner).depth =>
            {
                (*def, via.clone())
            }
            ExprKind::Call { def, scope: scope @ Scope::Instance { parent, .. }, args }
                if args.is_empty()
                    && via.is_none()
                    && **parent == Scope::Global
                    && self.spec.def(owner).depth == 0 =>
            {
                (*def, Some(Via { caller: owner, scope: scope.clone() }))
            }
            _ => {
                parts.push(Part { owner, expr, name, via });
                return Ok(());
            }
        };
        let callee = self.spec.def(target);
        let is_expandable = callee.params.is_empty()
            && matches!(callee.body, DefBody::Expr(_))
            && (callee.depth == 0 || inner.is_some())
            && self.part_level(via.as_ref(), &expr) > Level::Constant;
        if !is_expandable {
            parts.push(Part { owner, expr, name, via });
            return Ok(());
        }
        if expanding.contains(&target) {
            return Err(Error::config("Stack overflow while processing the specification."));
        }
        expanding.push(target);
        let body = Self::body(self.spec, target);
        let part = Part { owner: target, expr: body, name: callee.name.to_string(), via: inner };
        let result = self.expand(part, parts, expanding);
        expanding.pop();
        result
    }

    /// The level of `expr` in a frame `via` reaches, with the arguments of the instance.
    pub(super) fn part_level(&self, via: Option<&Via>, expr: &Expr) -> Level {
        let level = self.level(expr);
        match via {
            Some(Via { scope: Scope::Instance { args, .. }, .. }) => {
                args.iter().map(|arg| self.level(arg)).fold(level, Level::max)
            }
            _ => level,
        }
    }

    /// A zero-arity module-level definition for `expr` in the frame of `part`: the definition
    /// `expr` applies if it is a plain reference to one, and otherwise a new one.
    pub(super) fn part_def(&mut self, part: &Part, expr: &Expr) -> DefId {
        if let ExprKind::Call { def, scope: Scope::Global, args } = &expr.kind
            && args.is_empty()
            && self.spec.def(*def).params.is_empty()
        {
            return *self.overrides.get(def).unwrap_or(def);
        }
        let level = self.part_level(part.via.as_ref(), expr);
        let def = self.new_def(part.owner, expr.clone(), &part.name, level);
        match &part.via {
            None => def,
            // A definition in the instance's frame, which a module-level one calls.
            Some(Via { caller, scope }) => {
                let call = ExprKind::Call { def, scope: scope.clone(), args: Vec::new() };
                self.new_def(*caller, Expr::new(call, expr.span), &part.name, level)
            }
        }
    }

    /// A new zero-arity definition with `body`, in the frame of `owner`.
    fn new_def(&mut self, owner: DefId, body: Expr, name: &str, level: Level) -> DefId {
        let owner = self.spec.def(owner);
        let def = Def {
            name: Symbol::intern(name),
            module: owner.module,
            span: body.span,
            params: Vec::new(),
            body: DefBody::Expr(body),
            frame_size: owner.frame_size,
            depth: owner.depth,
            is_instantiated: owner.is_instantiated,
        };
        self.spec.defs.push(def);
        self.spec.levels.push(DefLevels {
            level,
            max_levels: Vec::new(),
            weights: Vec::new(),
            min_max_levels: Vec::new(),
            leibniz: Vec::new(),
        });
        DefId(self.spec.defs.len() as u32 - 1)
    }

    /// TLC's description of a range: `line 3, col 6 to line 3, col 14 of module M`.
    pub(super) fn describe(&self, owner: DefId, span: Span) -> String {
        describe_range(self.spec, self.spec.def(owner).module, span)
    }
}

/// TLC's description of a range of a module.
pub fn describe_range(spec: &Spec, module: tla_resolve::ModuleId, span: Span) -> String {
    let info = &spec.modules[module.index()];
    let (line, column) = span.line_column(&info.source);
    let last = Span::new(span.end.saturating_sub(1).max(span.start) as usize, span.end as usize);
    let (end_line, end_column) = last.line_column(&info.source);
    format!(
        "line {line}, col {column} to line {end_line}, col {end_column} of module {}",
        info.name
    )
}

/// The operand of `[]`, if the expression applies it.
pub(super) fn always(expr: &Expr) -> Option<&Expr> {
    match &expr.kind {
        ExprKind::Builtin { op: Builtin::Always, args } => args.first(),
        _ => None,
    }
}

pub(super) fn is_temporal_quantifier(expr: &Expr) -> bool {
    matches!(
        &expr.kind,
        ExprKind::UnboundedQuant {
            quantifier: Quantifier::TemporalExists | Quantifier::TemporalForall,
            ..
        }
    )
}
