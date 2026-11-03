//! The frames expressions are evaluated in, and what lazy values capture of them.

use std::ptr::NonNull;
use std::sync::{Arc, OnceLock};

use tla_resolve::{Expr, ModuleId, Spec};
use tla_value::Value;

use crate::{Operator, State};

/// What a slot of a frame holds.
#[derive(Clone)]
pub(crate) enum Slot {
    Value(Value),
    /// An argument of a definition, evaluated when the body reads it, as TLC's `LazyValue`.
    Thunk(Arc<Thunk>),
    /// The argument of a parameter that takes an operator, such as `F` in `Op(F(_))`.
    Op(Operator),
}

/// The parameters and bound variables of one call of a definition, and the frame the
/// definition captured.
///
/// Frames are shared through `Arc`. Evaluation writes slots of the current frame with
/// `Arc::make_mut`, so a lazy value that captured the frame keeps the values it saw, and no
/// frame can ever hold a reference to itself.
#[derive(Clone)]
pub(crate) struct Frame {
    pub slots: Vec<Slot>,
    pub parent: Option<Arc<Frame>>,
}

impl Frame {
    /// A frame for a definition that needs `size` slots, the first ones holding `args`.
    pub fn new(args: Vec<Slot>, size: usize, parent: Option<Arc<Frame>>) -> Self {
        let mut slots = args;
        slots.resize(size.max(slots.len()), Slot::Value(Value::FALSE));
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

/// An operator argument whose expression is evaluated where the body reads the parameter. It
/// reads the state of the reader, so that `x'` reads the argument in the next state, and caches
/// its value for reads in the state it was created in.
pub(crate) struct Thunk {
    pub expr: SpecRef<Expr>,
    pub captured: Captured,
    pub value: OnceLock<Value>,
}

/// Everything about the place an expression is evaluated in but the evaluator: what a lazy
/// value or a thunk keeps to evaluate an expression later.
#[derive(Clone)]
pub(crate) struct Captured {
    pub frame: Arc<Frame>,
    pub module: ModuleId,
    pub state: Option<State>,
    pub next: Option<State>,
    pub keep_lazy: bool,
}

impl Captured {
    pub fn env(&self) -> Env<'_> {
        Env {
            frame: self.frame.clone(),
            module: self.module,
            state: self.state.as_ref(),
            next: self.next.as_ref(),
            keep_lazy: self.keep_lazy,
        }
    }

    /// Whether `env` reads the states this was captured in.
    pub fn is_in_states_of(&self, env: &Env<'_>) -> bool {
        fn same(captured: Option<&State>, current: Option<&State>) -> bool {
            match (captured, current) {
                (Some(captured), Some(current)) => Arc::ptr_eq(captured, current),
                (None, None) => true,
                _ => false,
            }
        }
        same(self.state.as_ref(), env.state) && same(self.next.as_ref(), env.next)
    }
}

/// Where an expression is evaluated: the current frame, the module of the definition whose
/// text holds the expression, and the states.
pub(crate) struct Env<'a> {
    pub frame: Arc<Frame>,
    pub module: ModuleId,
    pub state: Option<&'a State>,
    /// The next state, which primed expressions read.
    pub next: Option<&'a State>,
    /// TLC's `EvalControl.KeepLazy`: set while evaluating the function of an application, so
    /// that a function constructor builds a lazy function and evaluates its body only where it
    /// is applied.
    pub keep_lazy: bool,
}

impl Env<'_> {
    pub fn set(&mut self, slot: usize, value: Value) {
        Arc::make_mut(&mut self.frame).slots[slot] = Slot::Value(value);
    }

    pub fn slot(&self, hops: usize, slot: usize) -> &Slot {
        &self.frame.up(hops).slots[slot]
    }

    pub fn capture(&self) -> Captured {
        Captured {
            frame: self.frame.clone(),
            module: self.module,
            state: self.state.cloned(),
            next: self.next.cloned(),
            keep_lazy: self.keep_lazy,
        }
    }
}

/// A reference into a [`Spec`] that keeps the spec alive, so that values evaluated later, such
/// as a lazily filtered set, can hold the expressions they evaluate.
pub(crate) struct SpecRef<T: ?Sized> {
    spec: Arc<Spec>,
    item: NonNull<T>,
}

// SAFETY: a `SpecRef` only gives shared access to a `T` inside an immutable `Spec`, which it keeps
// alive, so it can move and be shared across threads when `&T` can.
unsafe impl<T: Sync + ?Sized> Send for SpecRef<T> {}
unsafe impl<T: Sync + ?Sized> Sync for SpecRef<T> {}

impl<T: ?Sized> SpecRef<T> {
    /// # Safety
    ///
    /// `item` must be part of `*spec`.
    pub unsafe fn new(spec: &Arc<Spec>, item: &T) -> Self {
        Self { spec: spec.clone(), item: NonNull::from(item) }
    }

    pub fn get(&self) -> &T {
        // SAFETY: `item` points into the spec `self.spec` keeps alive. A spec behind an `Arc` is
        // never mutated or moved while another `Arc` to it exists, and it has no interior
        // mutability.
        unsafe { self.item.as_ref() }
    }

    pub fn spec(&self) -> &Arc<Spec> {
        &self.spec
    }
}
