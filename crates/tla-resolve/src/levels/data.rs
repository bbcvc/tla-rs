//! SANY's level information for an expression, and how applying an operator combines the
//! information of its arguments: tla-ts `levels.ts` and SANY's `OpApplNode.levelCheck`.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use super::layout::FrameId;
use crate::ir::{ConstId, Level, VarId};

/// A symbol whose level SANY leaves open: a declared constant or variable, or an operator parameter
/// or bound variable, which is a slot of a frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Param {
    Const(ConstId),
    Var(VarId),
    Slot(FrameId, usize),
}

/// The level of an expression and what it requires of the parameters it mentions.
#[derive(Clone, Debug, Default)]
pub(crate) struct Data {
    pub level: Level,
    /// The parameters whose levels count toward the level: SANY's `levelParams`.
    pub params: BTreeSet<Param>,
    /// The highest level each parameter may have: SANY's `levelConstraints`.
    pub constraints: BTreeMap<Param, Level>,
    /// The lowest level an operator parameter must allow for an argument, by parameter and
    /// argument: SANY's `argLevelConstraints`.
    pub arg_constraints: BTreeMap<(Param, usize), Level>,
    /// `(op, index, param)` when `param` is in argument `index` of the operator parameter `op`:
    /// SANY's `argLevelParams`.
    pub arg_params: BTreeSet<(Param, usize, Param)>,
}

impl Data {
    pub fn at(level: Level) -> Self {
        Self { level, ..Self::default() }
    }

    /// SANY's `SetOfLevelConstraints.put`, which keeps the lowest bound.
    pub fn constrain(&mut self, param: Param, level: Level) {
        let bound = self.constraints.entry(param).or_insert(Level::Temporal);
        *bound = (*bound).min(level);
    }

    /// SANY's `SetOfArgLevelConstraints.put`, which keeps the highest bound.
    pub fn require(&mut self, param: Param, index: usize, level: Level) {
        let bound = self.arg_constraints.entry((param, index)).or_insert(Level::Constant);
        *bound = (*bound).max(level);
    }

    /// Adds the constraints of `other` on the parameters `keep` accepts.
    pub fn add_constraints(&mut self, other: &Data, keep: impl Fn(Param) -> bool) {
        for (&param, &level) in &other.constraints {
            if keep(param) {
                self.constrain(param, level);
            }
        }
        for (&(param, index), &level) in &other.arg_constraints {
            self.require(param, index, level);
        }
        let kept = other.arg_params.iter().filter(|(_, _, param)| keep(*param));
        self.arg_params.extend(kept);
    }
}

/// How an operator treats its arguments: the level fields of SANY's `OpDefNode`.
#[derive(Clone, Debug)]
pub(crate) struct Operator {
    pub name: Rc<str>,
    /// The level of the body, and what it requires of parameters other than the formal ones.
    pub data: Data,
    pub formals: Vec<Param>,
    pub arity: usize,
    pub max_levels: Vec<Level>,
    pub weights: Vec<bool>,
    /// For each formal that takes an operator, the lowest level the operator must allow for each
    /// of its arguments.
    pub min_max_levels: Vec<Vec<Level>>,
    /// `(op, other, index)` when the body passes formal `other` as argument `index` of formal
    /// `op`, so the operator argument for `op` bounds the argument for `other`: SANY's
    /// `opLevelCond`.
    pub conditions: BTreeSet<(usize, usize, usize)>,
    /// The formals the operator isn't Leibniz in.
    pub non_leibniz: BTreeSet<usize>,
    /// Whether it is a built-in operator, whose last maximum level and weight hold for any further
    /// argument.
    pub is_builtin: bool,
}

impl Operator {
    /// A built-in operator, from SANY's `BuiltInOperators`.
    pub fn builtin(name: &str, level: u8, max_levels: &[u8], weights: &[u8]) -> Self {
        Self {
            name: name.into(),
            data: Data::at(level_of(level)),
            formals: Vec::new(),
            arity: max_levels.len(),
            max_levels: max_levels.iter().map(|&level| level_of(level)).collect(),
            weights: weights.iter().map(|&weight| weight == 1).collect(),
            min_max_levels: Vec::new(),
            // tla-ts: the built-in operators above the state level aren't Leibniz in anything.
            non_leibniz: if level > 1 { (0..max_levels.len()).collect() } else { BTreeSet::new() },
            conditions: BTreeSet::new(),
            is_builtin: true,
        }
    }

    /// An operator with the given formals, whose body has the level information `raw`, as tla-ts
    /// `analyzeOperator` makes one. `non_leibniz` are the parameters the body uses where the
    /// Leibniz rule fails. What `raw` says of the body's own bound variables, which `is_bound`
    /// tells apart, is dropped.
    pub fn defined(
        name: Rc<str>,
        raw: &Data,
        non_leibniz: &BTreeSet<Param>,
        formals: Vec<Param>,
        arities: &[usize],
        is_bound: impl Fn(Param) -> bool,
    ) -> Self {
        let is_formal = |param: Param| formals.contains(&param);
        let is_kept = |param: Param| !is_formal(param) && !is_bound(param);
        let mut conditions = BTreeSet::new();
        for (op_index, (&op, &arity)) in formals.iter().zip(arities).enumerate() {
            for (param_index, &param) in formals.iter().enumerate() {
                for index in 0..arity {
                    if raw.arg_params.contains(&(op, index, param)) {
                        conditions.insert((op_index, param_index, index));
                    }
                }
            }
        }
        let data = Data {
            level: raw.level,
            params: raw.params.iter().copied().filter(|&param| is_kept(param)).collect(),
            constraints: raw
                .constraints
                .iter()
                .filter(|&(&param, _)| is_kept(param))
                .map(|(&param, &level)| (param, level))
                .collect(),
            arg_constraints: raw
                .arg_constraints
                .iter()
                .filter(|&(&(param, _), _)| is_kept(param))
                .map(|(&key, &level)| (key, level))
                .collect(),
            arg_params: raw
                .arg_params
                .iter()
                .copied()
                .filter(|&(op, _, param)| {
                    let is_dropped = is_bound(op) || is_bound(param);
                    !(is_dropped || is_formal(op) && is_formal(param))
                })
                .collect(),
        };
        Self {
            name,
            max_levels: formals
                .iter()
                .map(|formal| raw.constraints.get(formal).copied().unwrap_or(Level::Temporal))
                .collect(),
            weights: formals.iter().map(|formal| raw.params.contains(formal)).collect(),
            min_max_levels: formals
                .iter()
                .zip(arities)
                .map(|(&formal, &arity)| {
                    (0..arity)
                        .map(|index| {
                            raw.arg_constraints.get(&(formal, index)).copied().unwrap_or_default()
                        })
                        .collect()
                })
                .collect(),
            non_leibniz: (0..formals.len())
                .filter(|&index| non_leibniz.contains(&formals[index]))
                .collect(),
            conditions,
            arity: formals.len(),
            formals,
            data,
            is_builtin: false,
        }
    }

    pub fn max_level(&self, index: usize) -> Level {
        let index = self.builtin_index(index);
        self.max_levels.get(index).copied().unwrap_or(Level::Temporal)
    }

    pub fn weight(&self, index: usize) -> bool {
        let index = self.builtin_index(index);
        self.weights.get(index).copied().unwrap_or(true)
    }

    fn builtin_index(&self, index: usize) -> usize {
        match self.is_builtin {
            true => index.min(self.max_levels.len().saturating_sub(1)),
            false => index,
        }
    }

    fn min_max_level(&self, operand: usize, index: usize) -> Level {
        let levels = self.min_max_levels.get(operand);
        levels.and_then(|levels| levels.get(index)).copied().unwrap_or_default()
    }

    fn has_condition(&self, operand: usize, other: usize, index: usize) -> bool {
        self.conditions.contains(&(operand, other, index))
    }
}

pub(crate) fn level_of(number: u8) -> Level {
    match number {
        0 => Level::Constant,
        1 => Level::State,
        2 => Level::Action,
        _ => Level::Temporal,
    }
}

/// An argument of an operator application.
#[derive(Clone, Debug, Default)]
pub(crate) struct Operand {
    pub data: Data,
    /// The operator, when the argument is a defined or built-in operator.
    pub operator: Option<Rc<Operator>>,
    /// The parameter and its arity, when the argument is an operator parameter or constant.
    pub declared: Option<(Param, usize)>,
}

impl Operand {
    pub fn value(data: Data) -> Self {
        Self { data, ..Self::default() }
    }
}

/// Applies an operator whose level SANY knows to `operands`, binding `bound` to elements of
/// `ranges`. Returns the level information of the application and the first level error SANY
/// reports in it.
pub(crate) fn apply(
    op: &Operator,
    operands: &[Operand],
    ranges: &[Data],
    bound: &[Param],
) -> (Data, Option<String>) {
    let error = check_arguments(op, operands, ranges);
    let is_bound = |param: &Param| bound.contains(param);
    let operand_of = |formal: Param| {
        let index = op.formals.iter().position(|&param| param == formal)?;
        operands.get(index)
    };

    let mut data = Data::at(op.data.level);
    data.params.extend(&op.data.params);
    for (index, operand) in operands.iter().enumerate() {
        if op.weight(index) {
            data.level = data.level.max(operand.data.level);
            data.params.extend(&operand.data.params);
        }
    }
    for range in ranges {
        data.level = data.level.max(range.level);
        data.params.extend(&range.params);
    }
    data.params.retain(|param| !is_bound(param));

    data.add_constraints(&op.data, |_| true);
    for operand in operands {
        data.add_constraints(&operand.data, |param| !is_bound(&param));
    }
    for range in ranges {
        data.add_constraints(range, |_| true);
    }
    for (index, operand) in operands.iter().enumerate() {
        for &param in operand.data.params.iter().filter(|param| !is_bound(param)) {
            data.constrain(param, op.max_level(index));
        }
    }
    for (index, operand) in operands.iter().enumerate() {
        let Some(argument) = &operand.operator else { continue };
        for (other_index, other) in operands.iter().enumerate() {
            for position in 0..argument.arity {
                if op.has_condition(index, other_index, position) {
                    for &param in &other.data.params {
                        data.constrain(param, argument.max_level(position));
                    }
                }
            }
        }
    }
    for &(formal, position, param) in &op.data.arg_params {
        if let Some(argument) = operand_of(formal).and_then(|operand| operand.operator.as_ref()) {
            data.constrain(param, argument.max_level(position));
        }
    }

    for (index, operand) in operands.iter().enumerate() {
        let Some((declared, arity)) = operand.declared else { continue };
        for position in 0..arity {
            data.require(declared, position, op.min_max_level(index, position));
            for (other_index, other) in operands.iter().enumerate() {
                if op.has_condition(index, other_index, position) {
                    data.require(declared, position, other.data.level);
                    for &param in &other.data.params {
                        data.arg_params.insert((declared, position, param));
                    }
                }
            }
        }
    }
    for &(formal, position, param) in &op.data.arg_params {
        match operand_of(formal) {
            Some(argument) => {
                data.require(formal, position, argument.data.level);
                if let Some((declared, _)) = argument.declared {
                    data.arg_params.insert((declared, position, param));
                }
            }
            None => match operand_of(param) {
                Some(value) => {
                    let params = value.data.params.iter();
                    data.arg_params.extend(params.map(|&param| (formal, position, param)));
                }
                None => {
                    data.arg_params.insert((formal, position, param));
                }
            },
        }
    }
    (data, error)
}

/// SANY's checks of the levels of the arguments of a defined or built-in operator.
fn check_arguments(op: &Operator, operands: &[Operand], ranges: &[Data]) -> Option<String> {
    let applying = format!("Level error in applying operator {}:\n", op.name);
    let exceeding = |index: usize| {
        format!(
            "{applying}The level of argument {} exceeds the maximum level allowed by the operator.",
            index + 1
        )
    };
    for (index, operand) in operands.iter().enumerate() {
        if operand.data.level > op.max_level(index) {
            return Some(exceeding(index));
        }
        let Some(argument) = &operand.operator else { continue };
        for position in 0..argument.arity {
            let minimum = op.min_max_level(index, position);
            if argument.max_level(position) < minimum {
                return Some(format!(
                    "{applying}The permitted level of argument {} of the operator argument {} \nmust be at least {}.",
                    position + 1,
                    index + 1,
                    minimum.number()
                ));
            }
        }
        for (other_index, other) in operands.iter().enumerate() {
            for position in 0..argument.arity {
                let is_bounded = op.has_condition(index, other_index, position);
                if is_bounded && other.data.level > argument.max_level(position) {
                    return Some(exceeding(other_index));
                }
            }
        }
    }
    ranges.iter().any(|range| range.level > Level::Action).then(|| {
        format!(
            "{applying}The level of the range for a bounded variable exceeds the maximum level allowed by the operator."
        )
    })
}

/// Applies a constant, variable, or operator parameter to `operands`, which SANY doesn't check.
pub(crate) fn apply_declared(param: Param, level: Level, operands: &[Operand]) -> Data {
    let mut data = Data::at(level);
    data.params.insert(param);
    for (index, operand) in operands.iter().enumerate() {
        data.level = data.level.max(operand.data.level);
        for &operand_param in &operand.data.params {
            data.params.insert(operand_param);
            data.arg_params.insert((param, index, operand_param));
        }
        data.add_constraints(&operand.data, |_| true);
        data.require(param, index, operand.data.level);
    }
    data
}

/// SANY's level, maximum argument levels, and weights of the built-in operators the resolved
/// program applies, by SANY's name for each (`tla2sany.semantic.BuiltInOperators`).
pub(crate) fn builtin_signature(name: &str) -> (u8, &'static [u8], &'static [u8]) {
    match name {
        "=" | "/=" | "\\in" | "\\notin" | "\\subseteq" | "\\union" | "\\intersect" | "\\"
        | "$FcnApply" => (0, &[2, 2], &[1, 1]),
        "\\land" | "\\lor" | "=>" | "\\equiv" => (0, &[3, 3], &[1, 1]),
        "\\lnot" | "$ConjList" | "$DisjList" | "$Case" | "$IfThenElse" | "$BoundedExists"
        | "$BoundedForall" | "$UnboundedExists" | "$UnboundedForall" | "$FcnConstructor"
        | "$RcdConstructor" => (0, &[3], &[1]),
        "SUBSET" | "UNION" | "DOMAIN" | "$SetEnumerate" | "$Tuple" | "$CartesianProd"
        | "$SetOfFcns" | "$SetOfRcds" | "$SubsetOf" | "$SetOfAll" | "$Except"
        | "$BoundedChoose" | "$UnboundedChoose" => (0, &[2], &[1]),
        "$RcdSelect" => (0, &[2, 0], &[1, 1]),
        "'" | "UNCHANGED" => (2, &[1], &[0]),
        "ENABLED" => (1, &[2], &[0]),
        "[]" | "<>" | "$TemporalExists" | "$TemporalForall" => (3, &[3], &[0]),
        "~>" | "-+->" => (3, &[3, 3], &[0, 0]),
        "\\cdot" => (2, &[2, 2], &[0, 0]),
        "$SquareAct" | "$AngleAct" => (2, &[2, 1], &[0, 0]),
        "$WF" | "$SF" => (3, &[1, 2], &[0, 0]),
        // BOOLEAN, STRING, TRUE, FALSE
        _ => (0, &[], &[]),
    }
}
