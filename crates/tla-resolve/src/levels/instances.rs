//! SANY's checks of the values an `INSTANCE` substitutes for the constants and variables of a
//! module, against the levels the module allows them (tla-ts `substitution-levels.ts` and SANY's
//! `InstanceNode.levelCheck`).

use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use tla_ast::Symbol;

use super::analyzer::{Analyzer, Body, Found};
use super::data::{Data, Operator, Param, apply};
use super::layout::{Instantiation, Substituted, SubstitutedValue};
use crate::ir::{DefId, ExprKind, Level, ModuleId};

/// What a module elaborated by itself defines and declares.
#[derive(Debug, Default)]
pub(crate) struct ModuleScope {
    /// Every definition its top level sees, those of its instances included.
    pub defs: Vec<DefId>,
    /// Its own assumptions.
    pub assumptions: Vec<DefId>,
    /// Its constants and variables, by name.
    pub declarations: Vec<(Symbol, Param)>,
    pub has_variables: bool,
}

/// What a module requires of the values substituted for its constants and variables, by name.
#[derive(Debug, Default)]
struct ModuleLevels {
    /// SANY's `ModuleNode.isConstant`: no variables, and only constant definitions.
    is_constant: bool,
    constraints: HashMap<Symbol, Level>,
    arg_constraints: HashMap<(Symbol, usize), Level>,
    arg_params: BTreeSet<(Symbol, usize, Symbol)>,
}

impl ModuleLevels {
    fn constrain(&mut self, name: Symbol, level: Level) {
        let bound = self.constraints.entry(name).or_insert(Level::Temporal);
        *bound = (*bound).min(level);
    }

    /// Adds what `data` requires of the module's constants and variables.
    fn add(&mut self, data: &Data, names: &HashMap<Param, Symbol>) {
        for (param, &level) in &data.constraints {
            if let Some(&name) = names.get(param) {
                self.constrain(name, level);
            }
        }
        for ((param, index), &level) in &data.arg_constraints {
            if let Some(&name) = names.get(param) {
                let bound = self.arg_constraints.entry((name, *index)).or_insert(Level::Constant);
                *bound = (*bound).max(level);
            }
        }
        for (op, index, param) in &data.arg_params {
            if let (Some(&op), Some(&param)) = (names.get(op), names.get(param)) {
                self.arg_params.insert((op, *index, param));
            }
        }
    }
}

/// The value substituted for a constant or variable.
struct Substitute {
    data: Data,
    /// The operator substituted for a constant operator, and whether it is a defined or built-in
    /// operator rather than a parameter.
    operator: Option<(Rc<Operator>, bool)>,
}

pub(crate) struct Instances<'s> {
    scopes: &'s HashMap<ModuleId, ModuleScope>,
    levels: HashMap<ModuleId, Option<Rc<ModuleLevels>>>,
    in_progress: HashSet<ModuleId>,
}

impl<'s> Instances<'s> {
    pub fn new(scopes: &'s HashMap<ModuleId, ModuleScope>) -> Self {
        Self { scopes, levels: HashMap::new(), in_progress: HashSet::new() }
    }

    /// Checks every instantiation SANY checks: those in the modules it checks by themselves.
    pub fn check(&mut self, analyzer: &mut Analyzer) {
        let layout = analyzer.layout;
        for instantiation in layout.instantiations.iter().filter(|item| !item.is_instantiated) {
            self.check_one(analyzer, instantiation);
        }
    }

    fn module_levels(
        &mut self,
        analyzer: &mut Analyzer,
        module: ModuleId,
    ) -> Option<Rc<ModuleLevels>> {
        if let Some(levels) = self.levels.get(&module) {
            return levels.clone();
        }
        let scope = self.scopes.get(&module)?;
        if !self.in_progress.insert(module) {
            return None;
        }
        let names: HashMap<Param, Symbol> =
            scope.declarations.iter().map(|&(name, param)| (param, name)).collect();
        let infos: Vec<_> = scope.defs.iter().map(|&def| analyzer.info(def)).collect();
        let mut levels = ModuleLevels {
            is_constant: !scope.has_variables
                && infos.iter().all(|info| info.own.data.level == Level::Constant),
            ..ModuleLevels::default()
        };
        if !levels.is_constant {
            for &(name, param) in &scope.declarations {
                if matches!(param, Param::Const(_)) {
                    levels.constrain(name, Level::Constant);
                }
            }
        }
        for info in &infos {
            levels.add(&info.own.data, &names);
        }
        for &def in &scope.assumptions {
            levels.add(&analyzer.info(def).own.data, &names);
        }
        let layout = analyzer.layout;
        let inner = layout.instantiations.iter();
        for instantiation in inner.filter(|item| item.instancer == module && !item.is_instantiated)
        {
            let data = self.instance_constraints(analyzer, instantiation);
            levels.add(&data, &names);
        }
        let levels = Rc::new(levels);
        self.in_progress.remove(&module);
        self.levels.insert(module, Some(levels.clone()));
        Some(levels)
    }

    /// What an instance requires of the parameters its substitutions mention: SANY's
    /// `Subst.getSubLCSet` of the instantiated module's constraints, and the substitutions' own.
    fn instance_constraints(
        &mut self,
        analyzer: &mut Analyzer,
        instantiation: &Instantiation,
    ) -> Data {
        let mut data = Data::default();
        let Some(target) = self.module_levels(analyzer, instantiation.module) else { return data };
        let substitutes: Vec<Substitute> = instantiation
            .substitutions
            .iter()
            .map(|substituted| substitute(analyzer, substituted))
            .collect();
        for (substituted, value) in instantiation.substitutions.iter().zip(&substitutes) {
            if let Some(&bound) = target.constraints.get(&substituted.name) {
                let level = if target.is_constant { bound } else { declared_level(substituted) };
                for &param in &value.data.params {
                    data.constrain(param, level);
                }
            }
            data.add_constraints(&value.data, |_| true);
        }
        let find = |name: Symbol| {
            let index = instantiation.substitutions.iter().position(|item| item.name == name)?;
            Some(&substitutes[index])
        };
        for &(op, index, param) in &target.arg_params {
            let (Some(op), Some(param)) = (find(op), find(param)) else { continue };
            if let Some((operator, true)) = &op.operator {
                for &mentioned in &param.data.params {
                    data.constrain(mentioned, operator.max_level(index));
                }
            }
        }
        data
    }

    fn check_one(&mut self, analyzer: &mut Analyzer, instantiation: &Instantiation) {
        let Some(target) = self.module_levels(analyzer, instantiation.module) else { return };
        let module = analyzer.spec.modules[instantiation.module.index()].name;
        let substitutes: Vec<Substitute> = instantiation
            .substitutions
            .iter()
            .map(|substituted| substitute(analyzer, substituted))
            .collect();
        let pairs = || instantiation.substitutions.iter().zip(&substitutes);
        let at_most = |name: Symbol, level: Level| {
            format!(
                "Level error in instantiating module '{module}':\nThe level of the expression or operator substituted for '{name}' \nmust be at most {}.",
                level.number()
            )
        };
        let mut messages = Vec::new();
        for (substituted, value) in pairs() {
            let declared = declared_level(substituted);
            if !target.is_constant && value.data.level > declared {
                messages.push(at_most(substituted.name, declared));
            }
            if let Some((operator, true)) = &value.operator
                && !operator.non_leibniz.is_empty()
            {
                messages.push(format!(
                    "Error in instantiating module '{module}':\n A non-Leibniz operator substituted for '{}'.",
                    substituted.name
                ));
            }
        }
        for (substituted, value) in pairs() {
            if let Some(&bound) = target.constraints.get(&substituted.name)
                && value.data.level > bound
            {
                messages.push(at_most(substituted.name, bound));
            }
            let Some((operator, true)) = &value.operator else { continue };
            for index in 0..substituted.arity {
                let key = (substituted.name, index);
                if let Some(&minimum) = target.arg_constraints.get(&key)
                    && operator.max_level(index) < minimum
                {
                    messages.push(format!(
                        "Level error in instantiating module '{module}':\nThe level of the argument {} of the operator {} \nmust be at least {}.",
                        index + 1,
                        operator.name,
                        minimum.number()
                    ));
                }
            }
        }
        let find = |name: Symbol| {
            let index = instantiation.substitutions.iter().position(|item| item.name == name)?;
            Some(&substitutes[index])
        };
        for &(op, index, param) in &target.arg_params {
            let (Some(op_value), Some(param_value)) = (find(op), find(param)) else { continue };
            let Some((operator, true)) = &op_value.operator else { continue };
            let maximum = operator.max_level(index);
            if param_value.data.level > maximum {
                // SANY numbers the argument from 0 here, and quotes the operator oddly.
                messages.push(format!(
                    "Level error when instantiating module '{module}':\nThe level of the argument {index} of the operator {op}' \nmust be at most {}.",
                    maximum.number()
                ));
            }
        }
        let mut seen = HashSet::new();
        for message in messages.into_iter().filter(|message| seen.insert(message.clone())) {
            analyzer.errors.push(Found {
                order: instantiation.order,
                module: instantiation.instancer,
                span: instantiation.span,
                message,
                is_reported: true,
            });
        }
    }
}

/// The level of a declared constant or variable, which a non-constant module allows no
/// substitution to exceed.
fn declared_level(substituted: &Substituted) -> Level {
    if substituted.is_variable { Level::State } else { Level::Constant }
}

fn substitute(analyzer: &mut Analyzer, substituted: &Substituted) -> Substitute {
    let def = match &substituted.value {
        SubstitutedValue::Inline(expr) => {
            let body = Body::new(None, Vec::new(), &[], &[]);
            return Substitute { data: analyzer.expr(&body, expr), operator: None };
        }
        SubstitutedValue::Def(def) => *def,
    };
    let own = analyzer.info(def).own.clone();
    if substituted.arity == 0 {
        return Substitute { data: apply(&own, &[], &[], &[]).0, operator: None };
    }
    // A substitution that resolution wrapped in a definition of its own, such as a LAMBDA or a
    // parameter, is the operator it applies.
    let is_wrapper = analyzer.layout.defs[def.index()].is_substitution;
    let (name, is_definition) = match &analyzer.spec.def(def).body {
        crate::ir::DefBody::Expr(expr) if is_wrapper => match &expr.kind {
            ExprKind::Call { def: inner, .. } => (analyzer.name(*inner), true),
            ExprKind::CallParam { .. } | ExprKind::CallConst { .. } => (own.name.clone(), false),
            _ => (own.name.clone(), true),
        },
        _ => (own.name.clone(), true),
    };
    let operator = Operator { name, ..(*own).clone() };
    Substitute { data: own.data.clone(), operator: Some((Rc::new(operator), is_definition)) }
}
