//! The temporal parts of the specification and the properties as liveness formula templates,
//! tla-ts `toLiveExpression` before evaluation: TLC expands the definitions a temporal formula
//! applies, and takes each part below temporal level as one formula it evaluates. Each such
//! part becomes a module-level definition that reaches the part's frame through the calls the
//! expansion went through.

use tla_ast::{Fairness, Quantifier};
use tla_resolve::{Builtin, Def, DefBody, DefId, DefLevels, Expr, ExprKind, Level, Scope};
use tla_value::Symbol;

use super::Planner;
use super::parts::Part;
use crate::Error;
use crate::liveness::template::Template;

/// How deep TLC expands definitions in a temporal formula before it reports a stack overflow.
const MAXIMUM_EXPANSION_DEPTH: usize = 100;

/// A call into the frame of a definition the expansion went into: `caller` applies the
/// definition through `scope` to `args`.
#[derive(Clone)]
struct Link {
    caller: DefId,
    scope: Scope,
    args: Vec<Expr>,
}

/// The frame an expression is in: that of `owner`, reached from a module-level definition
/// through `links`, outermost first.
#[derive(Clone)]
struct Frame {
    owner: DefId,
    links: Vec<Link>,
}

impl Planner<'_> {
    /// The template of the temporal formula `part`.
    pub(super) fn temporal(&mut self, part: &Part) -> Result<Template, Error> {
        let links = match &part.via {
            Some(via) => {
                vec![Link { caller: via.caller, scope: via.scope.clone(), args: Vec::new() }]
            }
            None => Vec::new(),
        };
        let frame = Frame { owner: part.owner, links };
        self.convert(&frame, &part.expr, 0)
    }

    /// The level of `expr` in `frame`, taking the arguments of the calls into it to be as high
    /// as any of them.
    fn frame_level(&self, frame: &Frame, expr: &Expr) -> Level {
        let mut level = self.level(expr);
        for link in &frame.links {
            let mut scope = &link.scope;
            while let Scope::Instance { parent, args } = scope {
                level = args.iter().map(|arg| self.level(arg)).fold(level, Level::max);
                scope = parent;
            }
            level = link.args.iter().map(|arg| self.level(arg)).fold(level, Level::max);
        }
        level
    }

    fn cannot_handle(&self, frame: &Frame, expr: &Expr) -> Error {
        Error::config(format!(
            "TLC cannot handle the temporal formula {}",
            self.describe(frame.owner, expr.span)
        ))
    }

    fn convert(&mut self, frame: &Frame, expr: &Expr, depth: usize) -> Result<Template, Error> {
        let level = self.frame_level(frame, expr);
        if level <= Level::Action {
            let def = self.wrap(frame, expr.clone());
            return Ok(match level {
                Level::Constant => Template::Constant(def),
                Level::State => Template::State(def),
                _ => Template::Action(def),
            });
        }
        let convert = |planner: &mut Self, expr: &Expr| planner.convert(frame, expr, depth);
        Ok(match &expr.kind {
            ExprKind::Builtin { op, args } => match op {
                Builtin::Always => Template::Always(Box::new(convert(self, &args[0])?)),
                Builtin::Eventually => Template::Eventually(Box::new(convert(self, &args[0])?)),
                Builtin::LeadsTo => Template::Always(Box::new(Template::Or(vec![
                    Template::Not(Box::new(convert(self, &args[0])?)),
                    Template::Eventually(Box::new(convert(self, &args[1])?)),
                ]))),
                Builtin::Not => Template::Not(Box::new(convert(self, &args[0])?)),
                Builtin::Implies => Template::Or(vec![
                    Template::Not(Box::new(convert(self, &args[0])?)),
                    convert(self, &args[1])?,
                ]),
                _ => return Err(self.cannot_handle(frame, expr)),
            },
            ExprKind::And(items) => Template::And(
                items.iter().map(|item| convert(self, item)).collect::<Result<_, _>>()?,
            ),
            ExprKind::Or(items) => Template::Or(
                items.iter().map(|item| convert(self, item)).collect::<Result<_, _>>()?,
            ),
            ExprKind::If { cond, then, otherwise } => {
                if self.frame_level(frame, cond) == Level::Constant {
                    Template::If {
                        condition: self.wrap(frame, (**cond).clone()),
                        then: Box::new(convert(self, then)?),
                        otherwise: Box::new(convert(self, otherwise)?),
                    }
                } else {
                    let condition = convert(self, cond)?;
                    Template::Or(vec![
                        Template::And(vec![condition.clone(), convert(self, then)?]),
                        Template::And(vec![
                            Template::Not(Box::new(condition)),
                            convert(self, otherwise)?,
                        ]),
                    ])
                }
            }
            ExprKind::Quant { quantifier, bounds, body } => {
                let is_constant = bounds
                    .iter()
                    .all(|bound| self.frame_level(frame, &bound.set) == Level::Constant);
                if !is_constant {
                    return Err(self.cannot_handle(frame, expr));
                }
                if !frame.links.is_empty() {
                    return Err(Error::unsupported(format!(
                        "a quantifier over a constant set inside an operator a temporal formula applies to arguments, at {}",
                        self.describe(frame.owner, expr.span)
                    )));
                }
                let bounds = bounds
                    .iter()
                    .map(|bound| (self.wrap(frame, bound.set.clone()), bound.pattern.clone()))
                    .collect();
                Template::Quantifier {
                    forall: matches!(quantifier, Quantifier::Forall),
                    bounds,
                    body: Box::new(convert(self, body)?),
                }
            }
            ExprKind::Fairness { fairness, sub, action } => {
                let span = action.span;
                let angle = Expr::new(
                    ExprKind::AngleAction { action: action.clone(), sub: sub.clone() },
                    span,
                );
                let enabled =
                    Expr::new(ExprKind::Builtin { op: Builtin::Enabled, args: vec![angle] }, span);
                let unchanged = Expr::new(
                    ExprKind::Builtin { op: Builtin::Unchanged, args: vec![(**sub).clone()] },
                    span,
                );
                Template::Fairness {
                    strong: matches!(fairness, Fairness::Strong),
                    enabled: self.wrap(frame, enabled),
                    action: self.wrap(frame, (**action).clone()),
                    unchanged: self.wrap(frame, unchanged),
                }
            }
            ExprKind::Call { def, scope, args } => {
                let target = *self.overrides.get(def).unwrap_or(def);
                let callee = self.spec.def(target);
                let DefBody::Expr(body) = &callee.body else {
                    return Err(self.cannot_handle(frame, expr));
                };
                if depth >= MAXIMUM_EXPANSION_DEPTH {
                    return Err(Error::config(
                        "Stack overflow while processing the specification.",
                    ));
                }
                let body = body.clone();
                let inner =
                    if matches!(scope, Scope::Global) && args.is_empty() && callee.depth == 0 {
                        Frame { owner: target, links: Vec::new() }
                    } else {
                        let mut links = frame.links.clone();
                        links.push(Link {
                            caller: frame.owner,
                            scope: scope.clone(),
                            args: args.clone(),
                        });
                        Frame { owner: target, links }
                    };
                self.convert(&inner, &body, depth + 1)?
            }
            _ => return Err(self.cannot_handle(frame, expr)),
        })
    }

    /// A module-level definition that evaluates `expr` in `frame`: a definition like the
    /// frame's owner with `expr` for its body, called through each link in a definition like
    /// the link's caller.
    fn wrap(&mut self, frame: &Frame, expr: Expr) -> DefId {
        let level = self.frame_level(frame, &expr);
        let span = expr.span;
        let mut def = self.like(frame.owner, expr, level);
        for link in frame.links.iter().rev() {
            let call = ExprKind::Call { def, scope: link.scope.clone(), args: link.args.clone() };
            def = self.like(link.caller, Expr::new(call, span), level);
        }
        def
    }

    /// A new definition with `body`, with the parameters and frame of `owner`.
    fn like(&mut self, owner: DefId, body: Expr, level: Level) -> DefId {
        let owner = self.spec.def(owner);
        let def = Def {
            name: Symbol::intern("liveness"),
            module: owner.module,
            span: body.span,
            params: owner.params.clone(),
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
}
