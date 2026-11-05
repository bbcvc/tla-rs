//! Analyses of a resolved specification that the evaluator makes once, before it evaluates.

use std::collections::{HashMap, HashSet};

use tla_tools_ast::{Quantifier, Symbol};
use tla_tools_resolve::{
    Bound, Builtin, DefBody, DefId, ExceptKey, Expr, ExprKind, Level, OpRef, Scope, Spec,
};

/// Whether each definition is one of a `LET` without parameters whose value the evaluator keeps
/// for the frame the `LET` is evaluated in, as TLC binds it to a `LazyValue`, by [`DefId`]. One
/// that calls an operator with effects or a random choice, or applies an operator parameter,
/// which could, is evaluated at each reference, as is one that builds a set with `UNION` or
/// `\cup`, which TLC builds anew each time (tla-ts `getReevaluatedDefinitions`).
pub(crate) fn cached_lets(spec: &Spec, is_computed_once: &[bool]) -> Vec<bool> {
    // In an action TLC evaluates a `LET` definition at each reference, so one that builds a set
    // with `UNION` or `\cup` builds it anew; in an expression it binds it to a `LazyValue`, as
    // tla-ts keeps a thunk.
    let in_action = Purity { spec, is_computed_once, allows_streamed_sets: false };
    let in_expression = Purity { spec, is_computed_once, allows_streamed_sets: true };
    let (mut pure_in_action, mut pure_in_expression) =
        (vec![None; spec.defs.len()], vec![None; spec.defs.len()]);
    let is_action = enclosing_actions(spec);
    (0..spec.defs.len())
        .map(|index| {
            let id = DefId(index as u32);
            let def = spec.def(id);
            def.depth > 0
                && def.params.is_empty()
                && match is_action[index] {
                    true => in_action.is_pure(id, &mut pure_in_action),
                    false => in_expression.is_pure(id, &mut pure_in_expression),
                }
        })
        .collect()
}

/// Whether each definition, by [`DefId`], sits in a module-level definition that is an action
/// or a temporal formula, or in none that can be told: where a `LET` can be the `LET` of an
/// action.
fn enclosing_actions(spec: &Spec) -> Vec<bool> {
    let is_action =
        |index: usize| spec.levels.get(index).is_none_or(|levels| levels.level >= Level::Action);
    let module_level: Vec<usize> =
        (0..spec.defs.len()).filter(|&index| spec.defs[index].depth == 0).collect();
    spec.defs
        .iter()
        .enumerate()
        .map(|(index, def)| {
            if def.depth == 0 {
                return is_action(index);
            }
            // The span of a definition is its name's, and its body follows.
            let enclosing = module_level.iter().find(|&&outer| {
                let outer = &spec.defs[outer];
                let end = match &outer.body {
                    DefBody::Expr(body) | DefBody::Function { body, .. } => body.span.end,
                };
                outer.module == def.module
                    && outer.span.start <= def.span.start
                    && def.span.end <= end
            });
            enclosing.is_none_or(|&outer| is_action(outer))
        })
        .collect()
}

/// Whether each definition is a module-level one without parameters, other than a constant TLC
/// computes once, whose value the evaluator keeps for the states it reads, by [`DefId`]: one
/// that a `LET` would keep, by the same rules, as evaluating it again in the same states gives
/// the same value.
pub(crate) fn cached_state_definitions(spec: &Spec, is_computed_once: &[bool]) -> Vec<bool> {
    // A value that holds a set TLC streams isn't kept, so one built with `UNION` or `\cup` can be.
    let purity = Purity { spec, is_computed_once, allows_streamed_sets: true };
    let mut is_pure: Vec<Option<bool>> = vec![None; spec.defs.len()];
    (0..spec.defs.len())
        .map(|index| {
            let id = DefId(index as u32);
            let def = spec.def(id);
            def.depth == 0
                && def.params.is_empty()
                && !is_computed_once[index]
                && purity.is_pure(id, &mut is_pure)
        })
        .collect()
}

/// The slots of the frame each definition of a `LET` is evaluated in that the definition may
/// read, as bits, by [`DefId`]: bit `s` for slot `s`, bit 63 for every slot from 63 on. A
/// definition whose reads can't be told reads them all.
pub(crate) fn let_reads(spec: &Spec) -> Vec<u64> {
    (0..spec.defs.len())
        .map(|index| {
            let id = DefId(index as u32);
            if spec.def(id).depth == 0 {
                return 0;
            }
            let mut visited = HashSet::new();
            definition_reads(spec, id, 1, &mut visited)
        })
        .collect()
}

fn slot_bit(slot: usize) -> u64 {
    1 << slot.min(63)
}

/// The slots of the frame `distance` frames up from the frame of `id` that the definition may read.
fn definition_reads(
    spec: &Spec,
    id: DefId,
    distance: usize,
    visited: &mut HashSet<(DefId, usize)>,
) -> u64 {
    if !visited.insert((id, distance)) {
        return 0;
    }
    let mut pending: Vec<&Expr> = match &spec.def(id).body {
        DefBody::Expr(body) => vec![body],
        DefBody::Function { bounds, body } => {
            bounds.iter().map(|bound| &bound.set).chain([body]).collect()
        }
    };
    let mut reads = 0;
    while let Some(expr) = pending.pop() {
        match &expr.kind {
            ExprKind::Local(local) | ExprKind::OpArg(OpRef::Param(local))
                if local.hops == distance =>
            {
                reads |= slot_bit(local.slot);
            }
            ExprKind::CallParam { param, .. } if param.hops == distance => {
                reads |= slot_bit(param.slot);
            }
            ExprKind::Call { def, scope, .. } | ExprKind::OpArg(OpRef::Def { def, scope }) => {
                match scope {
                    Scope::Global => {}
                    // The definition captures a frame at or below the one read.
                    Scope::Up(hops) if *hops <= distance => {
                        reads |= definition_reads(spec, *def, distance - hops + 1, visited);
                    }
                    Scope::Up(_) => {}
                    Scope::Instance { .. } => return u64::MAX,
                }
            }
            _ => {}
        }
        for_each_child(expr, &mut |child| pending.push(child));
    }
    reads
}

/// Whether each definition may read the next state, itself or through a definition it applies,
/// by [`DefId`]: one that primes an expression or holds an action. Unlike SANY's level, which
/// skips the arguments an operator ignores, this counts every argument.
pub(crate) fn reads_next_state(spec: &Spec) -> Vec<bool> {
    fn reads(spec: &Spec, id: DefId, known: &mut Vec<Option<bool>>) -> bool {
        if let Some(known) = known[id.index()] {
            return known;
        }
        known[id.index()] = Some(false);
        let mut pending: Vec<&Expr> = match &spec.def(id).body {
            DefBody::Expr(body) => vec![body],
            DefBody::Function { bounds, body } => {
                bounds.iter().map(|bound| &bound.set).chain([body]).collect()
            }
        };
        let mut found = false;
        while let Some(expr) = pending.pop() {
            found = match &expr.kind {
                ExprKind::Builtin {
                    op: Builtin::Prime | Builtin::Unchanged | Builtin::Cdot,
                    ..
                }
                | ExprKind::BoxAction { .. }
                | ExprKind::AngleAction { .. } => true,
                ExprKind::Call { def, .. } | ExprKind::OpArg(OpRef::Def { def, .. }) => {
                    reads(spec, *def, known)
                }
                _ => false,
            };
            if found {
                break;
            }
            for_each_child(expr, &mut |child| pending.push(child));
        }
        known[id.index()] = Some(found);
        found
    }
    let mut known = vec![None; spec.defs.len()];
    (0..spec.defs.len()).map(|index| reads(spec, DefId(index as u32), &mut known)).collect()
}

/// What makes evaluating a definition again differ from keeping its value.
struct Purity<'a> {
    spec: &'a Spec,
    is_computed_once: &'a [bool],
    /// Whether building a set with `UNION` or `\cup` is allowed.
    allows_streamed_sets: bool,
}

impl Purity<'_> {
    /// Whether the definition, and those it applies, have no effects and make no random
    /// choices: none calls such an operator or applies an operator parameter, which could.
    fn is_pure(&self, id: DefId, is_pure: &mut Vec<Option<bool>>) -> bool {
        if let Some(known) = is_pure[id.index()] {
            return known;
        }
        // A definition that refers to itself counts as pure meanwhile.
        is_pure[id.index()] = Some(true);
        let spec = self.spec;
        let def = spec.def(id);
        let module = spec.modules[def.module.index()].name.as_str();
        let pure = if crate::stdlib::is_impure(module, def.name.as_str()) {
            false
        } else {
            let mut pending: Vec<&Expr> = match &def.body {
                DefBody::Expr(body) => vec![body],
                DefBody::Function { bounds, body } => {
                    bounds.iter().map(|bound| &bound.set).chain([body]).collect()
                }
            };
            let mut pure = true;
            while let Some(expr) = pending.pop() {
                match &expr.kind {
                    ExprKind::CallParam { .. } => {
                        pure = false;
                        break;
                    }
                    ExprKind::Builtin { op: Builtin::Union | Builtin::Cup, .. }
                        if !self.allows_streamed_sets =>
                    {
                        pure = false;
                        break;
                    }
                    ExprKind::Call { def, .. } | ExprKind::OpArg(OpRef::Def { def, .. })
                        if !self.is_computed_once[def.index()] && !self.is_pure(*def, is_pure) =>
                    {
                        pure = false;
                        break;
                    }
                    _ => {}
                }
                for_each_child(expr, &mut |child| pending.push(child));
            }
            pure
        };
        is_pure[id.index()] = Some(pure);
        pure
    }
}

/// Whether `expr` reads a variable, itself or through a definition it applies.
pub(crate) fn mentions_variables(spec: &Spec, expr: &Expr) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        match &expr.kind {
            ExprKind::Var(_) => return true,
            ExprKind::Call { def, .. } | ExprKind::OpArg(OpRef::Def { def, .. })
                if spec
                    .levels
                    .get(def.index())
                    .is_some_and(|levels| levels.level != Level::Constant) =>
            {
                return true;
            }
            _ => for_each_child(expr, &mut |child| pending.push(child)),
        }
    }
    false
}

/// Whether the spec writes a string with a character above U+00FF, or reads strings with a JSON
/// deserializer, where they can reach a state (tla-ts `hasWideString`).
pub(crate) fn has_wide_string_literal(spec: &Spec) -> bool {
    let mut pending: Vec<&Expr> = Vec::new();
    for def in &spec.defs {
        match &def.body {
            DefBody::Expr(body) => pending.push(body),
            DefBody::Function { bounds, body } => {
                pending.push(body);
                pending.extend(bounds.iter().map(|bound| &bound.set));
            }
        }
    }
    while let Some(expr) = pending.pop() {
        match &expr.kind {
            ExprKind::Str(text) if is_wide(text.as_str()) => return true,
            ExprKind::Call { def, .. }
                if matches!(
                    spec.def(*def).name.as_str(),
                    "JsonDeserialize" | "ndJsonDeserialize"
                ) =>
            {
                return true;
            }
            _ => for_each_child(expr, &mut |child| pending.push(child)),
        }
    }
    false
}

/// Whether `text` has a character above U+00FF, which TLC fingerprints by its low byte.
pub(crate) fn is_wide(text: &str) -> bool {
    text.chars().any(|char| u32::from(char) > 0xff)
}

/// Whether each definition is a function definition whose body refers to the function, itself
/// or through a definition inside it, by [`DefId`].
pub(crate) fn recursive_functions(spec: &Spec) -> Vec<bool> {
    (0..spec.defs.len())
        .map(|index| {
            let def = DefId(index as u32);
            match &spec.def(def).body {
                DefBody::Function { body, .. } => refers_to(spec, def, body),
                DefBody::Expr(_) => false,
            }
        })
        .collect()
}

/// The function constructors in the body of a function definition that apply the function, by
/// address, which TLC builds lazily, as tla-ts's `markRecursiveConstructions` finds them: in
/// `f[i \in S] == [j \in T |-> ... f[i][j - 1] ...]`, building the function at once would apply
/// `f[i]` while it computes `f[i]`.
pub(crate) fn recursive_constructions(spec: &Spec) -> HashSet<usize> {
    let mut found = HashSet::new();
    for (index, info) in spec.defs.iter().enumerate() {
        let DefBody::Function { body, .. } = &info.body else { continue };
        let def = DefId(index as u32);
        let mut visited = HashSet::new();
        let mut pending = vec![body];
        while let Some(expr) = pending.pop() {
            match &expr.kind {
                ExprKind::Function { body: inner, .. } if refers_to(spec, def, inner) => {
                    found.insert(expr as *const Expr as usize);
                }
                // The definitions of the LETs in the body are part of it.
                ExprKind::Call { def: called, .. }
                    if spec.def(*called).depth > info.depth && visited.insert(*called) =>
                {
                    match &spec.def(*called).body {
                        DefBody::Expr(body) => pending.push(body),
                        DefBody::Function { bounds, body } => {
                            pending.push(body);
                            pending.extend(bounds.iter().map(|bound| &bound.set));
                        }
                    }
                }
                _ => {}
            }
            for_each_child(expr, &mut |child| pending.push(child));
        }
    }
    found
}

/// What TLC's ENABLED does with the variables of an instantiated module, as tla-ts rewrites it.
/// In the operand of an ENABLED in a module an `INSTANCE` substitutes into, and in what that
/// operand calls there, a primed variable of the module is a variable of its own, which TLC
/// binds by name, rather than the expression substituted for it.
#[derive(Default)]
pub(crate) struct InstanceEnabled {
    /// The ENABLEDs in instantiated definitions, by address.
    pub enabled: HashSet<usize>,
    /// The slot of the state being assigned that each variable of an instantiated module stands
    /// for in such an operand, and its name, by the address of the expression substituted for
    /// it: the slot of the root module's variable of that name, or one past them.
    pub variables: HashMap<usize, (usize, Symbol)>,
    /// The number of slots, the root module's variables and those past them.
    pub slots: usize,
}

/// Finds what [`InstanceEnabled`] describes, from where resolution recorded that an
/// instantiated module refers to its own variables.
pub(crate) fn instance_enabled(spec: &Spec) -> InstanceEnabled {
    let mut found = InstanceEnabled { slots: spec.variables.len(), ..InstanceEnabled::default() };
    let mut slots: HashMap<Symbol, usize> =
        spec.variables.iter().enumerate().map(|(index, var)| (var.name, index)).collect();
    for info in spec.defs.iter().filter(|info| info.is_instantiated) {
        let mut pending: Vec<&Expr> = match &info.body {
            DefBody::Expr(body) => vec![body],
            DefBody::Function { bounds, body } => {
                bounds.iter().map(|bound| &bound.set).chain([body]).collect()
            }
        };
        while let Some(expr) = pending.pop() {
            match &expr.kind {
                ExprKind::Builtin { op: Builtin::Enabled, .. } => {
                    found.enabled.insert(expr as *const Expr as usize);
                }
                // What an instance substitutes for a variable: an inlined variable, or a call of
                // the definition of a larger expression.
                ExprKind::Var(_) | ExprKind::Call { .. } => {
                    if let Some(&name) = spec.instance_variables.get(&(info.module, expr.span)) {
                        let next = found.slots;
                        let slot = *slots.entry(name).or_insert(next);
                        found.slots = found.slots.max(slot + 1);
                        found.variables.insert(expr as *const Expr as usize, (slot, name));
                    }
                }
                _ => {}
            }
            for_each_child(expr, &mut |child| pending.push(child));
        }
    }
    found
}

fn refers_to(spec: &Spec, target: DefId, body: &Expr) -> bool {
    let depth = spec.def(target).depth;
    let mut visited = HashSet::new();
    let mut pending = vec![body];
    while let Some(expr) = pending.pop() {
        if let ExprKind::Call { def, .. } | ExprKind::OpArg(OpRef::Def { def, .. }) = &expr.kind {
            if *def == target {
                return true;
            }
            if spec.def(*def).depth > depth && visited.insert(*def) {
                match &spec.def(*def).body {
                    DefBody::Expr(body) => pending.push(body),
                    DefBody::Function { bounds, body } => {
                        pending.push(body);
                        pending.extend(bounds.iter().map(|bound| &bound.set));
                    }
                }
            }
        }
        for_each_child(expr, &mut |child| pending.push(child));
    }
    false
}

/// The definition of `TLCEval` in TLC's standard module `TLC`, if the spec uses it.
pub(crate) fn tlc_eval(spec: &Spec) -> Option<DefId> {
    (0..spec.defs.len()).map(|index| DefId(index as u32)).find(|&id| {
        let def = spec.def(id);
        let module = &spec.modules[def.module.index()];
        module.is_standard && module.name.as_str() == "TLC" && def.name.as_str() == "TLCEval"
    })
}

/// The applications of `TLCEval` whose argument TLC's Java override normalizes, by the address
/// of each application. As tla-ts finds, TLC normalizes the value, and so fails on a set
/// enumeration it can't sort, only where it computes a constant once: for a constant argument,
/// in a module-level definition without parameters, outside every binder, and not in a module
/// that an `INSTANCE` substitutes into. Everywhere else `TLCEval(v)` is `v`.
pub(crate) fn normalizing_evaluations(spec: &Spec, tlc_eval: DefId) -> HashSet<usize> {
    let mut applications = HashSet::new();
    for def in &spec.defs {
        let DefBody::Expr(body) = &def.body else { continue };
        if def.depth > 0 || !def.params.is_empty() || def.is_instantiated {
            continue;
        }
        let mut pending = vec![body];
        while let Some(expr) = pending.pop() {
            if let ExprKind::Call { def, args, .. } = &expr.kind
                && *def == tlc_eval
                && args.iter().all(|arg| is_constant(spec, arg))
            {
                applications.insert(expr as *const Expr as usize);
            }
            for_each_unbound_child(expr, &mut |child| pending.push(child));
        }
    }
    applications
}

/// Whether an expression is constant, as SANY's levels decide it.
pub(super) fn is_constant(spec: &Spec, expr: &Expr) -> bool {
    let mut pending = vec![expr];
    while let Some(expr) = pending.pop() {
        let is_constant = match &expr.kind {
            ExprKind::Var(_)
            | ExprKind::BoxAction { .. }
            | ExprKind::AngleAction { .. }
            | ExprKind::Fairness { .. } => false,
            ExprKind::Builtin { op, .. } => !matches!(
                op,
                Builtin::Prime
                    | Builtin::Unchanged
                    | Builtin::Enabled
                    | Builtin::Always
                    | Builtin::Eventually
                    | Builtin::LeadsTo
                    | Builtin::PlusArrow
                    | Builtin::Cdot
            ),
            ExprKind::UnboundedQuant { quantifier, .. } => {
                !matches!(quantifier, Quantifier::TemporalForall | Quantifier::TemporalExists)
            }
            ExprKind::Call { def, .. } | ExprKind::OpArg(OpRef::Def { def, .. }) => {
                spec.levels.get(def.index()).is_none_or(|levels| levels.level == Level::Constant)
            }
            _ => true,
        };
        if !is_constant {
            return false;
        }
        for_each_child(expr, &mut |child| pending.push(child));
    }
    true
}

/// The subexpressions of `expr` evaluated in its own scope, outside the bound variables of the
/// quantifiers, comprehensions, functions, and `EXCEPT`s it is made of.
fn for_each_unbound_child<'e>(expr: &'e Expr, visit: &mut impl FnMut(&'e Expr)) {
    match &expr.kind {
        ExprKind::Quant { bounds, .. }
        | ExprKind::SetMap { bounds, .. }
        | ExprKind::Function { bounds, .. } => bounds.iter().for_each(|bound| visit(&bound.set)),
        ExprKind::SetFilter { bound, .. } => visit(&bound.set),
        ExprKind::Choose { set, .. } => set.iter().for_each(|set| visit(set)),
        ExprKind::UnboundedQuant { .. } => {}
        ExprKind::Except { base, updates } => {
            visit(base);
            for update in updates {
                for key in &update.path {
                    if let ExceptKey::Apply(args) = key {
                        args.iter().for_each(&mut *visit);
                    }
                }
            }
        }
        _ => for_each_child(expr, visit),
    }
}

pub(super) fn for_each_child<'e>(expr: &'e Expr, visit: &mut impl FnMut(&'e Expr)) {
    fn scope_args<'e>(scope: &'e Scope, visit: &mut impl FnMut(&'e Expr)) {
        if let Scope::Instance { parent, args } = scope {
            args.iter().for_each(&mut *visit);
            scope_args(parent, visit);
        }
    }
    fn bounds<'e>(bounds: &'e [Bound], visit: &mut impl FnMut(&'e Expr)) {
        bounds.iter().for_each(|bound| visit(&bound.set));
    }
    match &expr.kind {
        ExprKind::Bool(_)
        | ExprKind::Int(_)
        | ExprKind::Str(_)
        | ExprKind::Var(_)
        | ExprKind::Const(_)
        | ExprKind::Local(_) => {}
        ExprKind::Call { scope, args, .. } => {
            scope_args(scope, visit);
            args.iter().for_each(visit);
        }
        ExprKind::OpArg(OpRef::Def { scope, .. }) => scope_args(scope, visit),
        ExprKind::OpArg(_) => {}
        ExprKind::CallParam { args, .. }
        | ExprKind::CallConst { args, .. }
        | ExprKind::Builtin { args, .. }
        | ExprKind::And(args)
        | ExprKind::Or(args)
        | ExprKind::SetEnum(args)
        | ExprKind::Tuple(args)
        | ExprKind::Product(args) => args.iter().for_each(visit),
        ExprKind::If { cond, then, otherwise } => {
            visit(cond);
            visit(then);
            visit(otherwise);
        }
        ExprKind::Case { arms, other } => {
            for (guard, body) in arms {
                visit(guard);
                visit(body);
            }
            if let Some(other) = other {
                visit(other);
            }
        }
        ExprKind::Quant { bounds: quantified, body, .. }
        | ExprKind::SetMap { bounds: quantified, body }
        | ExprKind::Function { bounds: quantified, body } => {
            bounds(quantified, visit);
            visit(body);
        }
        ExprKind::UnboundedQuant { body, .. } => visit(body),
        ExprKind::Choose { set, body, .. } => {
            if let Some(set) = set {
                visit(set);
            }
            visit(body);
        }
        ExprKind::SetFilter { bound, pred } => {
            visit(&bound.set);
            visit(pred);
        }
        ExprKind::Record(fields) | ExprKind::RecordSet(fields) => {
            fields.iter().for_each(|(_, value)| visit(value));
        }
        ExprKind::FuncSet { domain: left, range: right }
        | ExprKind::BoxAction { action: left, sub: right }
        | ExprKind::AngleAction { action: left, sub: right }
        | ExprKind::Fairness { sub: left, action: right, .. } => {
            visit(left);
            visit(right);
        }
        ExprKind::FuncApp { func, args } => {
            visit(func);
            args.iter().for_each(visit);
        }
        ExprKind::Dot { record, .. } => visit(record),
        ExprKind::Except { base, updates } => {
            visit(base);
            for update in updates {
                for key in &update.path {
                    if let ExceptKey::Apply(args) = key {
                        args.iter().for_each(&mut *visit);
                    }
                }
                visit(&update.value);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use tla_tools_resolve::RootName;

    use crate::{EvalError, Evaluator, State, Value};

    const INNER: &str =
        "---- MODULE Inner ----\nCONSTANT E(_)\nMixed == 1 \\in E({1, \"a\"})\n====\n";

    fn evaluator() -> Evaluator {
        let source = r#"
---- MODULE Evaluations ----
EXTENDS TLC
VARIABLE x
Direct == 1 \in TLCEval({1, "a"})
Bound == \E y \in {1} : y \in TLCEval({y, "a"})
Param(v) == 1 \in TLCEval(v)
Called == Param({1, "a"})
I == INSTANCE Inner WITH E <- TLCEval
Instantiated == I!Mixed
Stateful == 1 \in TLCEval({1, x})
====
"#;
        let spec = tla_tools_resolve::resolve(source, &mut |name: &str| {
            (name == "Inner").then(|| INNER.to_owned())
        })
        .unwrap();
        Evaluator::new(Arc::new(spec), Vec::new())
    }

    fn eval(evaluator: &Evaluator, name: &str, state: Option<&State>) -> Result<Value, EvalError> {
        let Some(RootName::Def(def)) = evaluator.spec.lookup(name) else { panic!("{name}") };
        evaluator.eval_def(def, state)
    }

    /// tla-ts's NormalizationCases: TLCEval normalizes, and fails on a set enumeration it can't
    /// sort, only for a constant argument outside every binder and instance.
    #[test]
    fn normalizes_only_the_evaluations_tlc_computes_once() {
        let evaluator = evaluator();
        let error = eval(&evaluator, "Direct", None).unwrap_err().message;
        assert!(
            error.ends_with("Attempted to compare string \"a\" with non-string:\n1"),
            "{error}"
        );
        for name in ["Bound", "Called", "Instantiated"] {
            assert_eq!(eval(&evaluator, name, None).unwrap().to_string(), "TRUE", "{name}");
        }
        let state: State = vec![Value::str("a")].into();
        assert_eq!(eval(&evaluator, "Stateful", Some(&state)).unwrap().to_string(), "TRUE");
    }
}
