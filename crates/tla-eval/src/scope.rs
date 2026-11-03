//! Frames the model checker evaluates expressions of the spec in, outside the evaluation of a
//! definition: those of the calls it expands as it translates a temporal formula, with the
//! variables of the quantifiers it unrolls bound, as tla-ts's liveness translation keeps a scope.

use std::sync::Arc;

use tla_resolve::{DefId, Expr, ModuleId, Scope};
use tla_value::Value;

use crate::env::{Env, Frame, Slot, StateRef};
use crate::{Evaluator, Result, State};

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

impl Evaluator {
    /// The frame of a module-level definition without parameters, with no slot bound.
    pub fn module_frames(&self, def: DefId) -> Frames {
        let info = self.spec.def(def);
        Frames {
            frame: Arc::new(Frame::new(Vec::new(), info.frame_size, None)),
            module: info.module,
        }
    }

    /// The frames of a call of `def` through `scope` with `args`, a call written in the frames
    /// `caller`. The arguments are evaluated where the body reads them, as in any call.
    ///
    /// # Safety
    ///
    /// `args` and the arguments of an instance in `scope` must be expressions of this
    /// evaluator's spec, which values computed from them may keep referring to.
    pub unsafe fn call_frames(
        &self,
        caller: &Frames,
        def: DefId,
        scope: &Scope,
        args: &[Expr],
    ) -> Result<Frames> {
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

    /// Evaluates `expr` in `frames`: as a constant without a state, in `state`, or on the step
    /// from `state` to `next`.
    ///
    /// # Safety
    ///
    /// `expr` must be an expression of this evaluator's spec, written where `frames` are the
    /// frames of the definition it is in.
    pub unsafe fn eval_in(
        &self,
        frames: &Frames,
        expr: &Expr,
        state: Option<&State>,
        next: Option<&State>,
    ) -> Result<Value> {
        let mut env = Self::outside(frames, state, next);
        self.eval(expr, &mut env)
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
