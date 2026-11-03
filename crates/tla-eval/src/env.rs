//! The frames expressions are evaluated in.

use std::sync::Arc;

use tla_value::Value;

/// The parameters and bound variables of one call of a definition, and the frame the
/// definition captured.
///
/// Frames are shared through `Arc`. Evaluation writes slots of the current frame with
/// `Arc::make_mut`, so a lazy value that captured the frame keeps the values it saw.
#[derive(Clone)]
pub(crate) struct Frame {
    pub slots: Vec<Value>,
    pub parent: Option<Arc<Frame>>,
}

impl Frame {
    /// A frame for a definition that needs `size` slots, the first ones holding `args`.
    pub fn new(args: Vec<Value>, size: usize, parent: Option<Arc<Frame>>) -> Self {
        let mut slots = args;
        slots.resize(size.max(slots.len()), Value::FALSE);
        Self { slots, parent }
    }

    /// The frame `hops` frames up from this one.
    pub fn up(self: &Arc<Self>, hops: usize) -> &Arc<Frame> {
        let mut frame = self;
        for _ in 0..hops {
            frame = frame.parent.as_ref().expect("the resolver counts hops within the frame chain");
        }
        frame
    }
}
