//! Evaluation of resolved expressions.

use std::sync::Arc;

use tla_resolve::{Builtin, DefId};
use tla_value::Value;

use crate::env::Frame;
use crate::{Evaluator, Result, State};

impl Evaluator {
    /// Evaluates a definition without parameters at module level.
    pub(crate) fn eval_zero_arity(&self, def: DefId, state: Option<&State>) -> Result<Value> {
        self.call_def(def, None, Vec::new(), state)
    }

    /// Calls `def` with `args`, in a new frame whose parent is `parent`.
    pub(crate) fn call_def(
        &self,
        def: DefId,
        parent: Option<Arc<Frame>>,
        args: Vec<Value>,
        state: Option<&State>,
    ) -> Result<Value> {
        let _ = (def, parent, args, state);
        todo!("evaluate definitions")
    }

    /// Applies a built-in operator passed as an argument, such as `\cup` in `F(\cup)`.
    pub(crate) fn apply_builtin(
        &self,
        builtin: Builtin,
        args: &[Value],
    ) -> tla_value::Result<Value> {
        let _ = (builtin, args);
        todo!("apply built-in operators")
    }
}
