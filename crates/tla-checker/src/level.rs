//! The levels of expressions of the resolved program, which spec processing uses to sort the
//! conjuncts of a specification or property and to find what is constant, as TLC does. Both
//! kinds start from the levels the resolver computed, and raise to state level the operators
//! TLC overrides with Java methods that read the model checker's state, such as `TLCGet`:
//!
//! - TLC's level bound (`Spec.getLevelBound`, tla-ts `getLevel` and `isConstantLevel`) takes the
//!   level of every argument of an operator. Spec processing sorts parts and finds constants
//!   by it.
//! - SANY's level (tla-ts's level analyzer) takes the level of an argument only where the
//!   operator uses its parameter. TLC checks that an invariant is a state predicate by it.

use std::cell::RefCell;
use std::collections::HashMap;

use tla_resolve::{Builtin, DefBody, DefId, Expr, ExprKind, Level, OpRef, Scope, Spec};

/// The operators of TLC's modules whose Java overrides declare a state level, by module and
/// name: the list tla-eval computes constant definitions by.
pub const STATE_LEVEL_OPERATORS: &[(&str, &[&str])] = &[
    ("TLC", &["TLCGet", "TLCSet"]),
    (
        "TLCExt",
        &[
            "AssertError",
            "TLCGetOrDefault",
            "TLCGetAndSet",
            "Trace",
            "CounterExample",
            "TLCDefer",
            "PickSuccessor",
            "TLCCache",
            "TLCEvalDefinition",
        ],
    ),
    ("_Possible", &["_Track", "_Counts", "_CheckName", "_PrintCounts"]),
    (
        "Json",
        &[
            "ToJson",
            "ToJsonArray",
            "ToJsonObject",
            "JsonSerialize",
            "ndJsonSerialize",
            "JsonDeserialize",
            "ndJsonDeserialize",
        ],
    ),
    ("Randomization", &["RandomSubset", "RandomSetOfSubsets", "TestRandomSetOfSubsets"]),
    ("IOUtils", &["IOExec", "IOEnvExec", "IOExecTemplate", "IOEnvExecTemplate"]),
];

/// The operators TLC takes for variables when it checks the definitions the configuration
/// substitutes for constants, as tla-ts lists them.
pub const SUBSTITUTION_STATE_LEVEL_OPERATORS: &[(&str, &[&str])] =
    &[("TLC", &["TLCGet"]), ("TLCExt", &["Trace", "CounterExample"])];

/// The levels of definitions, remembered. Definitions added to the spec later don't change the
/// levels of earlier ones.
pub struct Levels {
    definitions: RefCell<HashMap<DefId, Level>>,
    /// Whether an argument counts only where the operator uses its parameter, as in SANY.
    is_weighted: bool,
    operators: &'static [(&'static str, &'static [&'static str])],
}

impl Default for Levels {
    fn default() -> Self {
        Self::tlc()
    }
}

impl Levels {
    /// TLC's level bound.
    pub fn tlc() -> Self {
        Self::new(false, STATE_LEVEL_OPERATORS)
    }

    /// SANY's levels, with the given operators at state level.
    pub fn sany(operators: &'static [(&'static str, &'static [&'static str])]) -> Self {
        Self::new(true, operators)
    }

    fn new(
        is_weighted: bool,
        operators: &'static [(&'static str, &'static [&'static str])],
    ) -> Self {
        Self { definitions: RefCell::default(), is_weighted, operators }
    }

    /// The level of a definition with its parameters taken to be constants.
    pub fn def_level(&self, spec: &Spec, def: DefId) -> Level {
        if let Some(&level) = self.definitions.borrow().get(&def) {
            return level;
        }
        // A recursive definition sees itself as a constant while its level is computed.
        self.definitions.borrow_mut().insert(def, Level::Constant);
        let level = if is_state_level_operator(spec, def, self.operators) {
            Level::State
        } else {
            let body = match &spec.def(def).body {
                DefBody::Expr(expr) => self.level(spec, expr),
                DefBody::Function { bounds, body } => bounds
                    .iter()
                    .map(|bound| self.level(spec, &bound.set))
                    .fold(self.level(spec, body), Level::max),
            };
            body.max(spec.level(def))
        };
        self.definitions.borrow_mut().insert(def, level);
        level
    }

    /// The level of `expr`: what it can mention.
    pub fn level(&self, spec: &Spec, expr: &Expr) -> Level {
        let all = |exprs: &mut dyn Iterator<Item = &Expr>| {
            exprs.map(|expr| self.level(spec, expr)).fold(Level::Constant, Level::max)
        };
        match &expr.kind {
            ExprKind::Bool(_) | ExprKind::Int(_) | ExprKind::Str(_) | ExprKind::Const(_) => {
                Level::Constant
            }
            ExprKind::Local(_) => Level::Constant,
            ExprKind::Var(_) => Level::State,
            ExprKind::Call { def, scope, args } => {
                let outer = instance_args(scope)
                    .map(|arg| self.level(spec, arg))
                    .fold(self.def_level(spec, *def), Level::max);
                let own: Vec<Level> = args.iter().map(|arg| self.level(spec, arg)).collect();
                let applied = if self.is_weighted {
                    spec.def_levels(*def).applied(&own)
                } else {
                    own.into_iter().fold(Level::Constant, Level::max)
                };
                applied.max(outer)
            }
            ExprKind::CallParam { args, .. } | ExprKind::CallConst { args, .. } => {
                all(&mut args.iter())
            }
            ExprKind::OpArg(op) => match op {
                OpRef::Def { def, .. } => self.def_level(spec, *def),
                _ => Level::Constant,
            },
            ExprKind::Builtin { op, args } => {
                let operands = all(&mut args.iter());
                match op {
                    Builtin::Prime | Builtin::Unchanged | Builtin::Cdot => {
                        Level::Action.max(operands)
                    }
                    Builtin::Enabled => Level::State,
                    Builtin::Always
                    | Builtin::Eventually
                    | Builtin::LeadsTo
                    | Builtin::PlusArrow => Level::Temporal,
                    _ => operands,
                }
            }
            ExprKind::BoxAction { action, sub } | ExprKind::AngleAction { action, sub } => {
                Level::Action.max(self.level(spec, action)).max(self.level(spec, sub))
            }
            ExprKind::Fairness { .. } => Level::Temporal,
            ExprKind::UnboundedQuant { quantifier, body, .. } => match quantifier {
                tla_ast::Quantifier::TemporalForall | tla_ast::Quantifier::TemporalExists => {
                    Level::Temporal
                }
                _ => self.level(spec, body),
            },
            _ => children(expr)
                .into_iter()
                .map(|child| self.level(spec, child))
                .fold(Level::Constant, Level::max),
        }
    }
}

fn is_state_level_operator(spec: &Spec, def: DefId, operators: &[(&str, &[&str])]) -> bool {
    let def = spec.def(def);
    let module = &spec.modules[def.module.index()];
    def.depth == 0
        && operators.iter().any(|(name, operators)| {
            *name == module.name.as_str() && operators.contains(&def.name.as_str())
        })
}

/// The arguments of the parameterized instances in a call's scope, outermost first.
fn instance_args(scope: &Scope) -> impl Iterator<Item = &Expr> {
    let mut groups = Vec::new();
    let mut scope = scope;
    while let Scope::Instance { parent, args } = scope {
        groups.push(args);
        scope = parent;
    }
    groups.into_iter().rev().flatten()
}

/// The subexpressions of an expression with no level of its own.
fn children(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::And(items)
        | ExprKind::Or(items)
        | ExprKind::SetEnum(items)
        | ExprKind::Tuple(items)
        | ExprKind::Product(items) => items.iter().collect(),
        ExprKind::If { cond, then, otherwise } => vec![cond, then, otherwise],
        ExprKind::Case { arms, other } => {
            let mut children: Vec<&Expr> =
                arms.iter().flat_map(|(guard, arm)| [guard, arm]).collect();
            children.extend(other.as_deref());
            children
        }
        ExprKind::Quant { bounds, body, .. }
        | ExprKind::SetMap { bounds, body }
        | ExprKind::Function { bounds, body } => {
            bounds.iter().map(|bound| &bound.set).chain([&**body]).collect()
        }
        ExprKind::Choose { set, body, .. } => set.as_deref().into_iter().chain([&**body]).collect(),
        ExprKind::SetFilter { bound, pred } => vec![&bound.set, pred],
        ExprKind::Record(fields) | ExprKind::RecordSet(fields) => {
            fields.iter().map(|(_, value)| value).collect()
        }
        ExprKind::FuncSet { domain, range } => vec![domain, range],
        ExprKind::FuncApp { func, args } => [&**func].into_iter().chain(args).collect(),
        ExprKind::Dot { record, .. } => vec![record],
        ExprKind::Except { base, updates } => {
            let mut children = vec![&**base];
            for update in updates {
                for key in &update.path {
                    if let tla_resolve::ExceptKey::Apply(args) = key {
                        children.extend(args);
                    }
                }
                children.push(&update.value);
            }
            children
        }
        _ => Vec::new(),
    }
}

/// Calls `each` with every subexpression of `expr`, those of the instance arguments of a call
/// included.
pub fn for_each_child<'e>(expr: &'e Expr, each: &mut dyn FnMut(&'e Expr)) {
    let all = |exprs: &'e [Expr], each: &mut dyn FnMut(&'e Expr)| exprs.iter().for_each(&mut *each);
    match &expr.kind {
        ExprKind::Call { scope, args, .. } => {
            instance_args(scope).for_each(&mut *each);
            all(args, each);
        }
        ExprKind::CallParam { args, .. }
        | ExprKind::CallConst { args, .. }
        | ExprKind::Builtin { args, .. } => all(args, each),
        ExprKind::UnboundedQuant { body, .. } => each(body),
        ExprKind::BoxAction { action, sub }
        | ExprKind::AngleAction { action, sub }
        | ExprKind::Fairness { action, sub, .. } => {
            each(action);
            each(sub);
        }
        _ => children(expr).into_iter().for_each(each),
    }
}

/// Calls `each` with `expr` and every expression in it.
pub fn visit<'e>(expr: &'e Expr, each: &mut dyn FnMut(&'e Expr)) {
    each(expr);
    for_each_child(expr, &mut |child| visit(child, each));
}
