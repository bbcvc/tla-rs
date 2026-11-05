//! The temporal parts of the specification and the properties, which liveness checking
//! translates once the evaluator exists, as tla-ts `toLiveExpression` does with values at hand.
//! Spec processing makes each part a module-level definition, which reaches the part's frame
//! through the instance it is in, and adds a definition `ENABLED <<A>>_v` beside the definition
//! of each fairness condition `WF_v(A)` or `SF_v(A)`, for the translation to evaluate.

use std::collections::HashMap;

use tla_tools_ast::Span;
use tla_tools_resolve::{Builtin, Def, DefBody, DefId, DefLevels, Expr, ExprKind, Level};
use tla_tools_value::Symbol;

use super::Planner;
use super::parts::Part;

/// The definition `ENABLED <<A>>_v` of each fairness condition, by the definition whose body
/// holds the condition and where it is written.
pub type EnabledDefs = HashMap<(DefId, Span), DefId>;

impl Planner<'_> {
    /// A module-level definition of the temporal formula `part`: one like the part's owner with
    /// the formula for its body, called through the part's instance if it is in one.
    pub(super) fn temporal(&mut self, part: &Part) -> DefId {
        let span = part.expr.span;
        let def = self.like(part.owner, part.expr.clone(), Level::Temporal);
        match &part.via {
            None => def,
            Some(via) => {
                let call = ExprKind::Call { def, scope: via.scope.clone(), args: Vec::new() };
                self.like(via.caller, Expr::new(call, span), Level::Temporal)
            }
        }
    }

    /// The definition `ENABLED <<A>>_v` beside the definition of each fairness condition.
    pub(super) fn enabled_defs(&mut self) -> EnabledDefs {
        let mut found: Vec<(DefId, Span, Expr)> = Vec::new();
        for (index, def) in self.spec.defs.iter().enumerate() {
            let body = match &def.body {
                DefBody::Expr(body) => body,
                DefBody::Function { body, .. } => body,
            };
            fairness_conditions(body, &mut |expr, action, sub| {
                let angle = Expr::new(
                    ExprKind::AngleAction {
                        action: Box::new(action.clone()),
                        sub: Box::new(sub.clone()),
                    },
                    action.span,
                );
                let enabled = Expr::new(
                    ExprKind::Builtin { op: Builtin::Enabled, args: vec![angle] },
                    action.span,
                );
                found.push((DefId(index as u32), expr.span, enabled));
            });
        }
        found
            .into_iter()
            .map(|(owner, span, enabled)| ((owner, span), self.like(owner, enabled, Level::State)))
            .collect()
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

/// Calls `each` with every fairness condition in `expr`, with its action and subscript.
fn fairness_conditions(expr: &Expr, each: &mut dyn FnMut(&Expr, &Expr, &Expr)) {
    if let ExprKind::Fairness { action, sub, .. } = &expr.kind {
        each(expr, action, sub);
    }
    crate::level::for_each_child(expr, &mut |child| fairness_conditions(child, each));
}
