//! Frames the model checker evaluates expressions of the spec in, outside the evaluation of a
//! definition: those of the calls it expands as it translates a temporal formula, with the
//! variables of the quantifiers it unrolls bound, as tla-ts's liveness translation keeps a scope.
//!
//! Values computed from an expression may keep referring to it, so these take expressions only
//! as [`SpecExpr`]s: an expression found in the body of a definition of the evaluator's spec,
//! which the handle keeps alive.

use std::sync::Arc;

use tla_tools_resolve::{DefBody, DefId, Expr, ExprKind, ModuleId, OpRef, Scope};
use tla_tools_value::Value;

use crate::env::{Env, Frame, Slot, SpecRef, StateRef};
use crate::{EvalError, Evaluator, Result, State};

/// The frame of a call of a definition, with the frames it captured, and the module whose text
/// holds the definition.
#[derive(Clone)]
pub struct Frames {
    frame: Arc<Frame>,
    module: ModuleId,
}

impl Frames {
    /// The module whose text the expressions evaluated in these frames are in.
    pub fn module(&self) -> ModuleId {
        self.module
    }
}

/// An expression of the body of a definition of an evaluator's spec.
#[derive(Clone)]
pub struct SpecExpr(SpecRef<Expr>);

impl SpecExpr {
    pub fn get(&self) -> &Expr {
        self.0.get()
    }
}

impl Evaluator {
    /// `expr` as an expression of the spec, if it is in the body of `def`: the body itself, a
    /// part of it, or a part of a bound of a function definition.
    pub fn spec_expr(&self, def: DefId, expr: &Expr) -> Option<SpecExpr> {
        let found = match &self.spec.def(def).body {
            DefBody::Expr(body) => contains(body, expr),
            DefBody::Function { bounds, body } => {
                contains(body, expr) || bounds.iter().any(|bound| contains(&bound.set, expr))
            }
        };
        // SAFETY: `expr` is a node of the spec, found by its address in a definition's body.
        found.then(|| SpecExpr(unsafe { SpecRef::new(&self.spec, expr) }))
    }

    /// The frame of a module-level definition without parameters, with no slot bound.
    pub fn module_frames(&self, def: DefId) -> Frames {
        let info = self.spec.def(def);
        Frames {
            frame: Arc::new(Frame::new(Vec::new(), info.frame_size, None)),
            module: info.module,
        }
    }

    /// The frames of `def` applied as the call `call` applies a definition, with its scope and
    /// arguments, written in the frames `caller`. `def` is the definition the call applies, or
    /// the one the configuration replaces it with. The arguments are evaluated where the body
    /// reads them, as in any call.
    pub fn call_frames(&self, caller: &Frames, call: &SpecExpr, def: DefId) -> Result<Frames> {
        let call = self.own(call)?;
        let ExprKind::Call { scope, args, .. } = &call.kind else {
            return Err(self.outside_error("call_frames needs a call"));
        };
        let env = Self::outside(caller, None, None);
        let parent = self.scope_frame(scope, &env)?;
        let slots = args.iter().map(|arg| self.arg_slot(arg, &env)).collect::<Result<Vec<_>>>()?;
        let info = self.spec.def(def);
        Ok(Frames {
            frame: Arc::new(Frame::new(slots, info.frame_size, parent)),
            module: info.module,
        })
    }

    /// `frames` with slot `slot` of the innermost frame bound to `value`, as a quantifier binds
    /// its variable.
    pub fn bind(&self, frames: &Frames, slot: usize, value: Value) -> Frames {
        let mut frame = (*frames.frame).clone();
        frame.slots[slot] = Slot::Value(value);
        Frames { frame: Arc::new(frame), module: frames.module }
    }

    /// Evaluates `expr` in `frames`, the frames of the definition it is written in: as a
    /// constant without a state, in `state`, or on the step from `state` to `next`.
    pub fn eval_in(
        &self,
        frames: &Frames,
        expr: &SpecExpr,
        state: Option<&State>,
        next: Option<&State>,
    ) -> Result<Value> {
        let expr = self.own(expr)?;
        let mut env = Self::outside(frames, state, next);
        self.eval(expr, &mut env)
    }

    /// The expression of a handle of this evaluator's spec.
    fn own<'s>(&self, expr: &'s SpecExpr) -> Result<&'s Expr> {
        if !Arc::ptr_eq(expr.0.spec(), &self.spec) {
            return Err(self.outside_error("An expression of another specification was evaluated"));
        }
        Ok(expr.get())
    }

    fn outside_error(&self, message: &str) -> EvalError {
        EvalError {
            message: message.to_owned(),
            module: tla_tools_value::Symbol::intern(""),
            span: Default::default(),
            line: 0,
            column: 0,
            incomplete: None,
            call_stack: Vec::new(),
            is_standard: false,
        }
    }

    fn outside<'a>(frames: &Frames, state: Option<&'a State>, next: Option<&'a State>) -> Env<'a> {
        Env {
            frame: frames.frame.clone(),
            module: frames.module,
            state: state.map(StateRef::Complete),
            next: next.map(StateRef::Complete),
            keep_lazy: false,
            enabled: Default::default(),
        }
    }
}

/// Whether `target` is `expr` or one of its parts, by address.
fn contains(expr: &Expr, target: &Expr) -> bool {
    if std::ptr::eq(expr, target) {
        return true;
    }
    let any = |exprs: &[Expr]| exprs.iter().any(|expr| contains(expr, target));
    let in_scope = |scope: &Scope| {
        let mut scope = scope;
        while let Scope::Instance { parent, args } = scope {
            if any(args) {
                return true;
            }
            scope = parent;
        }
        false
    };
    let in_bounds = |bounds: &[tla_tools_resolve::Bound]| {
        bounds.iter().any(|bound| contains(&bound.set, target))
    };
    let one = |expr: &Expr| contains(expr, target);
    match &expr.kind {
        ExprKind::Bool(_)
        | ExprKind::Int(_)
        | ExprKind::Str(_)
        | ExprKind::Var(_)
        | ExprKind::Const(_)
        | ExprKind::Local(_) => false,
        ExprKind::Call { scope, args, .. } => in_scope(scope) || any(args),
        ExprKind::OpArg(OpRef::Def { scope, .. }) => in_scope(scope),
        ExprKind::OpArg(_) => false,
        ExprKind::CallParam { args, .. }
        | ExprKind::CallConst { args, .. }
        | ExprKind::Builtin { args, .. }
        | ExprKind::And(args)
        | ExprKind::Or(args)
        | ExprKind::SetEnum(args)
        | ExprKind::Tuple(args)
        | ExprKind::Product(args) => any(args),
        ExprKind::If { cond, then, otherwise } => one(cond) || one(then) || one(otherwise),
        ExprKind::Case { arms, other } => {
            arms.iter().any(|(guard, arm)| one(guard) || one(arm))
                || other.as_deref().is_some_and(one)
        }
        ExprKind::Quant { bounds, body, .. }
        | ExprKind::SetMap { body, bounds }
        | ExprKind::Function { bounds, body } => in_bounds(bounds) || one(body),
        ExprKind::UnboundedQuant { body, .. } => one(body),
        ExprKind::Choose { set, body, .. } => set.as_deref().is_some_and(one) || one(body),
        ExprKind::SetFilter { bound, pred } => one(&bound.set) || one(pred),
        ExprKind::Record(fields) | ExprKind::RecordSet(fields) => {
            fields.iter().any(|(_, value)| one(value))
        }
        ExprKind::FuncSet { domain, range } => one(domain) || one(range),
        ExprKind::FuncApp { func, args } => one(func) || any(args),
        ExprKind::Dot { record, .. } => one(record),
        ExprKind::Except { base, updates } => {
            one(base)
                || updates.iter().any(|update| {
                    one(&update.value)
                        || update.path.iter().any(|key| match key {
                            tla_tools_resolve::ExceptKey::Apply(args) => any(args),
                            tla_tools_resolve::ExceptKey::Field(_) => false,
                        })
                })
        }
        ExprKind::BoxAction { action, sub }
        | ExprKind::AngleAction { action, sub }
        | ExprKind::Fairness { action, sub, .. } => one(action) || one(sub),
    }
}
