//! What the resolver records for the level pass about the program it builds, beyond the IR: the
//! frame each definition's parameters live in, the `LET`s of each definition, the `RECURSIVE`
//! sections, and the instantiations to check.

use std::rc::Rc;

use tla_ast::{Span, Symbol};

use crate::ir::{DefId, Expr, ModuleId};

/// A frame of parameters and bound variables, by the order the resolver created it in.
pub(crate) type FrameId = usize;

#[derive(Debug, Default)]
pub(crate) struct Layout {
    pub frames: Vec<FrameLayout>,
    /// By [`DefId`].
    pub defs: Vec<DefLayout>,
    pub instantiations: Vec<Instantiation>,
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
    /// Whether the definition is the value substituted for a constant or variable of an instance.
    pub is_substitution: bool,
    /// The `RECURSIVE` section the definition was made in: the definitions from a `RECURSIVE`
    /// declaration up to the definition of every operator it declared.
    pub section: Option<usize>,
    /// Whether a `RECURSIVE` declaration declared the definition.
    pub is_recursive: bool,
}

/// An `INSTANCE` of a module with constants or variables.
#[derive(Debug)]
pub(crate) struct Instantiation {
    pub module: ModuleId,
    pub instancer: ModuleId,
    /// The whole `INSTANCE`, or `I == INSTANCE ...`, where SANY reports its errors.
    pub span: Span,
    /// The value of each constant and variable of the module, in the order the module declares
    /// them.
    pub substitutions: Vec<Substituted>,
    pub is_instantiated: bool,
    /// The number of definitions made before the instantiation, to order its errors among theirs.
    pub order: usize,
}

#[derive(Debug)]
pub(crate) struct Substituted {
    pub name: Symbol,
    pub is_variable: bool,
    pub arity: usize,
    pub value: SubstitutedValue,
}

#[derive(Debug)]
pub(crate) enum SubstitutedValue {
    Def(DefId),
    /// A value simple enough for resolution to copy into each use.
    Inline(Expr),
}
