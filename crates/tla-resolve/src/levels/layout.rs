//! What the resolver records for the level pass about the program it builds, beyond the IR: the
//! frame each definition's parameters live in, the `LET`s of each definition, and the `RECURSIVE`
//! sections.

use std::rc::Rc;

use tla_ast::Span;

use crate::ir::DefId;

/// A frame of parameters and bound variables, by the order the resolver created it in.
pub(crate) type FrameId = usize;

#[derive(Debug, Default)]
pub(crate) struct Layout {
    pub frames: Vec<FrameLayout>,
    /// By [`DefId`].
    pub defs: Vec<DefLayout>,
}

#[derive(Debug)]
pub(crate) struct FrameLayout {
    /// The frame around this one, which a definition with this frame captures.
    pub parent: Option<FrameId>,
    /// The arity of each parameter in the frame: a definition's parameters, or a parameterized
    /// instance's.
    pub params: Vec<usize>,
}

#[derive(Debug, Default)]
pub(crate) struct DefLayout {
    /// The frame of the definition's own parameters and bound variables.
    pub frame: Option<FrameId>,
    /// The definitions of the `LET`s in the body, which SANY checks with the body even when the
    /// body doesn't use them.
    pub lets: Vec<DefId>,
    /// The span of the body of each `LET` in the body. Resolution replaces a `LET` with its body,
    /// which SANY tells apart from an operator application.
    pub let_bodies: Vec<Span>,
    /// `I!J!` for a definition of the named instances `I` and `J`, which SANY names `I!J!Op`.
    pub qualifier: Option<Rc<str>>,
    /// Whether resolution made the definition elaborating a module under the substitutions of an
    /// `INSTANCE`. SANY checks the module's own definitions instead.
    pub is_instantiated: bool,
    /// The `RECURSIVE` section the definition was made in: the definitions from a `RECURSIVE`
    /// declaration up to the definition of every operator it declared.
    pub section: Option<usize>,
    /// Whether a `RECURSIVE` declaration declared the definition.
    pub is_recursive: bool,
}
