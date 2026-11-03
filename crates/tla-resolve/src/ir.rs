//! The resolved program: every name in it refers to a state variable, a constant, a local slot,
//! or a definition, so evaluation never looks a name up.
//!
//! Evaluation keeps a chain of frames. Calling a definition creates a frame for its parameters
//! and the variables its body binds. A definition nested in another, such as a `LET` definition,
//! a `LAMBDA`, or a definition of a parameterized instance, captures the frame it was defined in,
//! and [`Scope`] says how to find that frame from the call site.

use std::collections::HashMap;
use std::sync::Arc;

use tla_ast::{Fairness, Quantifier, Span, Symbol};

macro_rules! id {
    ($($(#[$doc:meta])* $name:ident,)*) => {
        $(
            $(#[$doc])*
            #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
            pub struct $name(pub u32);

            impl $name {
                pub fn index(self) -> usize {
                    self.0 as usize
                }
            }
        )*
    };
}

id! {
    /// A state variable. Its index is its slot in a state.
    VarId,
    /// A declared constant, whose value comes from the model configuration.
    ConstId,
    DefId,
    ModuleId,
}

/// The whole program a root module and the modules it uses resolve to.
#[derive(Clone, Debug)]
pub struct Spec {
    pub modules: Vec<ModuleInfo>,
    pub variables: Vec<Declaration>,
    pub constants: Vec<Declaration>,
    pub defs: Vec<Def>,
    /// The `ASSUME`s of every module the spec uses, each as a zero-arity definition. Axioms,
    /// which TLC doesn't check, are left out.
    pub assumptions: Vec<DefId>,
    /// The names visible at the top level of the root module, which the configuration refers to.
    pub root: HashMap<Symbol, RootName>,
}

impl Spec {
    pub fn def(&self, id: DefId) -> &Def {
        &self.defs[id.index()]
    }

    pub fn lookup(&self, name: &str) -> Option<RootName> {
        Symbol::get(name).and_then(|symbol| self.root.get(&symbol).copied())
    }
}

#[derive(Clone, Debug)]
pub struct ModuleInfo {
    pub name: Symbol,
    pub source: Arc<str>,
    /// Whether the module is one of TLC's standard modules, bundled with tla-rs.
    pub is_standard: bool,
}

/// A `VARIABLE` or `CONSTANT` declaration.
#[derive(Clone, Debug)]
pub struct Declaration {
    pub name: Symbol,
    /// Zero for a variable or an ordinary constant, `n` for a constant such as `F(_, _)`.
    pub arity: usize,
    pub module: ModuleId,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RootName {
    Var(VarId),
    Const(ConstId),
    Def(DefId),
}

#[derive(Clone, Debug)]
pub struct Def {
    pub name: Symbol,
    /// The module whose text holds the definition.
    pub module: ModuleId,
    pub span: Span,
    /// The arity of each parameter: zero for an ordinary parameter, `n` for `F(_, ...)`.
    pub params: Vec<usize>,
    pub body: DefBody,
    /// The slots a frame of this definition needs: its parameters and every variable its body
    /// binds.
    pub frame_size: usize,
    /// The number of frames around the definition. Zero for a module-level definition.
    pub depth: usize,
}

#[derive(Clone, Debug)]
pub enum DefBody {
    Expr(Expr),
    /// `f[x \in S] == body`. The body may apply the function recursively.
    Function {
        bounds: Vec<Bound>,
        body: Expr,
    },
}

/// An operator parameter or a bound variable: slot `slot` of the frame `hops` frames up from the
/// current one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Local {
    pub hops: usize,
    pub slot: usize,
}

/// Where the frame a called definition captures comes from.
#[derive(Clone, Debug, PartialEq)]
pub enum Scope {
    /// A module-level definition, which captures no frame.
    Global,
    /// The frame this many hops up from the current one. `Up(0)` is the current frame, which a
    /// `LET` definition or `LAMBDA` in it captures.
    Up(usize),
    /// A new frame for the arguments of a parameterized instance, as in `I(args)!Op`, whose own
    /// parent is `parent`.
    Instance { parent: Box<Scope>, args: Vec<Expr> },
}

#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn new(kind: ExprKind, span: Span) -> Self {
        Self { kind, span }
    }
}

/// An operator TLA+ defines itself, which no module can redefine.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Builtin {
    Boolean,
    String,
    /// `/\` passed as an argument. Applied directly, a conjunction is [`ExprKind::And`].
    And,
    /// `\/` passed as an argument. Applied directly, a disjunction is [`ExprKind::Or`].
    Or,
    Eq,
    Neq,
    Not,
    Implies,
    Equiv,
    In,
    NotIn,
    SubsetEq,
    Cup,
    Cap,
    SetMinus,
    Powerset,
    Union,
    Domain,
    Prime,
    Unchanged,
    Enabled,
    Always,
    Eventually,
    LeadsTo,
    PlusArrow,
    /// `\cdot`, the composition of actions.
    Cdot,
}

impl Builtin {
    pub fn arity(self) -> usize {
        match self {
            Self::Boolean | Self::String => 0,
            Self::Not
            | Self::Powerset
            | Self::Union
            | Self::Domain
            | Self::Prime
            | Self::Unchanged
            | Self::Enabled
            | Self::Always
            | Self::Eventually => 1,
            _ => 2,
        }
    }
}

/// An operator passed as an argument, as `+` in `F(+)` or `LAMBDA x : x` in `F(LAMBDA x : x)`.
#[derive(Clone, Debug, PartialEq)]
pub enum OpRef {
    Def { def: DefId, scope: Scope },
    Param(Local),
    Const(ConstId),
    Builtin(Builtin),
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Bool(bool),
    Int(i64),
    Str(Symbol),
    Var(VarId),
    Const(ConstId),
    Local(Local),
    Call {
        def: DefId,
        scope: Scope,
        args: Vec<Expr>,
    },
    /// Applies an operator parameter such as `F` in `Op(F(_)) == F(1)`.
    CallParam {
        param: Local,
        args: Vec<Expr>,
    },
    /// Applies a constant operator such as `F` in `CONSTANT F(_)`.
    CallConst {
        id: ConstId,
        args: Vec<Expr>,
    },
    Builtin {
        op: Builtin,
        args: Vec<Expr>,
    },
    OpArg(OpRef),
    And(Vec<Expr>),
    Or(Vec<Expr>),
    If {
        cond: Box<Expr>,
        then: Box<Expr>,
        otherwise: Box<Expr>,
    },
    Case {
        arms: Vec<(Expr, Expr)>,
        other: Option<Box<Expr>>,
    },
    /// `\A` or `\E` over bounded sets.
    Quant {
        quantifier: Quantifier,
        bounds: Vec<Bound>,
        body: Box<Expr>,
    },
    /// `\A x : P`, `\E x : P`, `\AA x : P`, or `\EE x : P`.
    UnboundedQuant {
        quantifier: Quantifier,
        slots: Vec<usize>,
        body: Box<Expr>,
    },
    Choose {
        pattern: Pattern,
        set: Option<Box<Expr>>,
        body: Box<Expr>,
    },
    SetEnum(Vec<Expr>),
    SetFilter {
        bound: Box<Bound>,
        pred: Box<Expr>,
    },
    SetMap {
        body: Box<Expr>,
        bounds: Vec<Bound>,
    },
    Tuple(Vec<Expr>),
    Record(Vec<(Symbol, Expr)>),
    RecordSet(Vec<(Symbol, Expr)>),
    FuncSet {
        domain: Box<Expr>,
        range: Box<Expr>,
    },
    Function {
        bounds: Vec<Bound>,
        body: Box<Expr>,
    },
    FuncApp {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    Dot {
        record: Box<Expr>,
        field: Symbol,
    },
    Except {
        base: Box<Expr>,
        updates: Vec<ExceptUpdate>,
    },
    Product(Vec<Expr>),
    BoxAction {
        action: Box<Expr>,
        sub: Box<Expr>,
    },
    AngleAction {
        action: Box<Expr>,
        sub: Box<Expr>,
    },
    Fairness {
        fairness: Fairness,
        sub: Box<Expr>,
        action: Box<Expr>,
    },
}

/// The slots of the current frame a bound introduces.
#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    /// `x, y \in S`: each slot ranges over the set.
    Names(Vec<usize>),
    /// `<<x, y>> \in S`: the slots destructure each tuple in the set.
    Tuple(Vec<usize>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Bound {
    pub pattern: Pattern,
    pub set: Expr,
}

#[derive(Clone, Debug, PartialEq)]
pub struct ExceptUpdate {
    pub path: Vec<ExceptKey>,
    /// The slot that holds the old value, which `@` in `value` refers to.
    pub at: usize,
    pub value: Expr,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExceptKey {
    Apply(Vec<Expr>),
    Field(Symbol),
}
