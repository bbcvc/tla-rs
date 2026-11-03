//! Syntax tree for TLA+ modules.
//!
//! The tree is purely syntactic: names are unresolved [`Symbol`]s, and operator applications keep
//! the operator as written. Resolution into variables, constants, and definitions happens later.

mod expr;
mod op;

pub use expr::{
    Bound, CaseArm, Component, ExceptKey, ExceptUpdate, Expr, ExprKind, Fairness, Pattern,
    Quantifier,
};
pub use op::Op;
pub use tla_intern::Symbol;

/// A byte range in the source text.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start: start as u32, end: end as u32 }
    }

    /// The 1-based line and column of the start of the span. Columns count characters.
    pub fn line_column(self, source: &str) -> (usize, usize) {
        let before = &source[..self.start as usize];
        let line = before.matches('\n').count() + 1;
        let line_start = before.rfind('\n').map_or(0, |index| index + 1);
        (line, before[line_start..].chars().count() + 1)
    }
}

/// An identifier or operator name with the place it was written.
///
/// Symbolic operators such as `++` are named by [`Op::name`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Name {
    pub symbol: Symbol,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Module {
    pub name: Name,
    pub extends: Vec<Name>,
    pub units: Vec<Unit>,
    pub span: Span,
}

/// A top-level item of a module, or a definition in a `LET`.
#[derive(Clone, Debug, PartialEq)]
pub enum Unit {
    Variables(Vec<Name>),
    Constants(Vec<OpDecl>),
    Recursive(Vec<OpDecl>),
    Operator(OperatorDef),
    Function(FunctionDef),
    /// An unnamed `INSTANCE M WITH ...`.
    Instance(Instance),
    /// `Name(params) == INSTANCE M WITH ...`.
    ModuleDef(ModuleDef),
    Assume(Assume),
    Theorem(Theorem),
    Module(Module),
}

/// A declared operator: a constant, a `RECURSIVE` declaration, or an operator parameter.
/// `F(_, _)` has arity 2. A plain identifier has arity 0.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OpDecl {
    pub name: Name,
    pub arity: usize,
}

/// `Name(params) == body`, including symbolic definitions such as `a ++ b == ...`.
#[derive(Clone, Debug, PartialEq)]
pub struct OperatorDef {
    pub name: Name,
    pub params: Vec<OpDecl>,
    pub body: Expr,
    pub is_local: bool,
}

/// `f[x \in S, y \in T] == body`.
#[derive(Clone, Debug, PartialEq)]
pub struct FunctionDef {
    pub name: Name,
    pub bounds: Vec<Bound>,
    pub body: Expr,
    pub is_local: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Instance {
    pub module: Name,
    pub substitutions: Vec<Substitution>,
    pub is_local: bool,
    pub span: Span,
}

/// `name <- value` in an `INSTANCE ... WITH`.
#[derive(Clone, Debug, PartialEq)]
pub struct Substitution {
    pub name: Name,
    pub value: Expr,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ModuleDef {
    pub name: Name,
    pub params: Vec<OpDecl>,
    pub instance: Instance,
    pub is_local: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Assume {
    pub name: Option<Name>,
    pub expr: Expr,
    /// Written `AXIOM` rather than `ASSUME` or `ASSUMPTION`. TLC doesn't check axioms.
    pub is_axiom: bool,
}

/// A theorem. TLC doesn't check theorems, so the proof isn't kept. A named theorem defines its
/// name as its statement.
#[derive(Clone, Debug, PartialEq)]
pub struct Theorem {
    pub name: Option<Name>,
    /// The statement, unless it is an `ASSUME ... PROVE`.
    pub statement: Option<Expr>,
    pub span: Span,
}

#[cfg(test)]
mod tests {
    use super::Span;

    #[test]
    fn line_column_counts_characters() {
        let source = "a\n∧ b";
        let offset = source.find('b').unwrap();
        assert_eq!(Span::new(offset, offset + 1).line_column(source), (2, 3));
        assert_eq!(Span::new(0, 1).line_column(source), (1, 1));
    }
}
