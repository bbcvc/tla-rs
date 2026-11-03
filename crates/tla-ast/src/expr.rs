use crate::{Name, Op, Span, Unit};

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

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Bool(bool),
    Int(i64),
    Str(tla_intern::Symbol),
    /// `x`, `Op(a, b)`, or a built-in set such as `Nat` or `BOOLEAN`. An operator passed as an
    /// argument, such as `+` in `F(+)`, is an `Apply` of its [`Op::name`] with no arguments.
    Apply {
        name: Name,
        args: Vec<Expr>,
    },
    /// `M!Op(a)` or `M(x)!N!Op`: an operator reached through named instances.
    Qualified {
        path: Vec<Component>,
        name: Name,
        args: Vec<Expr>,
    },
    Lambda {
        params: Vec<Name>,
        body: Box<Expr>,
    },
    Prefix {
        op: Op,
        arg: Box<Expr>,
    },
    Infix {
        op: Op,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Postfix {
        op: Op,
        arg: Box<Expr>,
    },
    /// A conjunction, from `/\` or a bulleted list. Infix chains are flattened.
    And(Vec<Expr>),
    /// A disjunction, from `\/` or a bulleted list. Infix chains are flattened.
    Or(Vec<Expr>),
    If {
        cond: Box<Expr>,
        then: Box<Expr>,
        otherwise: Box<Expr>,
    },
    Case {
        arms: Vec<CaseArm>,
        other: Option<Box<Expr>>,
    },
    /// `LET defs IN body`. The definitions are operators, functions, instances, and `RECURSIVE`
    /// declarations.
    Let {
        defs: Vec<Unit>,
        body: Box<Expr>,
    },
    /// `\A x \in S : body` or `\E x \in S : body`.
    Quant {
        quantifier: Quantifier,
        bounds: Vec<Bound>,
        body: Box<Expr>,
    },
    /// `\A x : body`, `\E x : body`, `\AA x : body`, or `\EE x : body`.
    UnboundedQuant {
        quantifier: Quantifier,
        names: Vec<Name>,
        body: Box<Expr>,
    },
    /// `CHOOSE x \in S : body`, or `CHOOSE x : body` when `set` is `None`.
    Choose {
        pattern: Pattern,
        set: Option<Box<Expr>>,
        body: Box<Expr>,
    },
    SetEnum(Vec<Expr>),
    /// `{x \in S : pred}`.
    SetFilter {
        bound: Box<Bound>,
        pred: Box<Expr>,
    },
    /// `{body : x \in S, y \in T}`.
    SetMap {
        body: Box<Expr>,
        bounds: Vec<Bound>,
    },
    Tuple(Vec<Expr>),
    /// `[a |-> 1, b |-> 2]`.
    Record(Vec<(Name, Expr)>),
    /// `[a : S, b : T]`.
    RecordSet(Vec<(Name, Expr)>),
    /// `[S -> T]`.
    FuncSet {
        domain: Box<Expr>,
        range: Box<Expr>,
    },
    /// `[x \in S |-> body]`.
    Function {
        bounds: Vec<Bound>,
        body: Box<Expr>,
    },
    /// `f[a]`, or `f[a, b]`, which applies `f` to the tuple `<<a, b>>`.
    FuncApp {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    /// `r.field`.
    Dot {
        record: Box<Expr>,
        field: Name,
    },
    Except {
        base: Box<Expr>,
        updates: Vec<ExceptUpdate>,
    },
    /// `@` inside an `EXCEPT` update.
    At,
    /// `S \X T \X U`. A chain is one n-ary product. Parentheses keep their nesting.
    Product(Vec<Expr>),
    /// `[A]_v`.
    BoxAction {
        action: Box<Expr>,
        sub: Box<Expr>,
    },
    /// `<<A>>_v`.
    AngleAction {
        action: Box<Expr>,
        sub: Box<Expr>,
    },
    /// `WF_v(A)` or `SF_v(A)`.
    Fairness {
        fairness: Fairness,
        sub: Box<Expr>,
        action: Box<Expr>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Quantifier {
    Forall,
    Exists,
    TemporalForall,
    TemporalExists,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fairness {
    Weak,
    Strong,
}

/// The names a bound introduces.
#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    /// `x, y \in S`: each name ranges over the set.
    Names(Vec<Name>),
    /// `<<x, y>> \in S`: the names destructure each tuple in the set.
    Tuple(Vec<Name>),
}

/// `x \in S`, `x, y \in S`, or `<<x, y>> \in S`.
#[derive(Clone, Debug, PartialEq)]
pub struct Bound {
    pub pattern: Pattern,
    pub set: Expr,
}

#[derive(Clone, Debug, PartialEq)]
pub struct CaseArm {
    pub guard: Expr,
    pub body: Expr,
}

/// One `M` or `M(args)` step in a qualified name such as `M(1)!Op`.
#[derive(Clone, Debug, PartialEq)]
pub struct Component {
    pub name: Name,
    pub args: Vec<Expr>,
}

/// `![a].b = value` in an `EXCEPT`.
#[derive(Clone, Debug, PartialEq)]
pub struct ExceptUpdate {
    pub path: Vec<ExceptKey>,
    pub value: Expr,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExceptKey {
    /// `[a]`, or `[a, b]` for the tuple `<<a, b>>`.
    Apply(Vec<Expr>),
    /// `.field`.
    Field(Name),
}
