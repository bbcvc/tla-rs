//! SANY's level checking: the level of every definition, and the level errors SANY reports.
//!
//! An expression's level is what it can mention: constants, unprimed variables, primed variables,
//! or temporal operators. SANY computes the level of every definition, with the highest level each
//! parameter allows and the lowest level each operator parameter requires, and rejects
//! expressions TLA+ forbids, such as `[]A` for an action `A`, or an argument above the level its
//! operator allows. The pass follows tla-ts `levels.ts`, `sany/levels.ts`, and
//! `substitution-levels.ts`, which port SANY's `levelCheck` methods.
//!
//! The levels of a definition come from its resolved body. Resolution copies the definitions of
//! an instantiated module with the substitutions in place, so their levels are those of the
//! substituted bodies. SANY instead checks each module once by itself and checks each `INSTANCE`
//! against what that module allows its constants and variables, so errors are only reported in
//! modules resolution elaborated by themselves. A module resolution only elaborated under
//! substitutions is elaborated by itself for the pass, and those definitions dropped after.

mod analyzer;
mod data;
mod expr;
mod instances;
pub(crate) mod layout;
mod leibniz;

use std::collections::{BTreeSet, HashMap, HashSet};

use tla_tools_ast::Span;

use self::analyzer::{Analyzer, Found};
use self::data::Param;
use self::instances::{Instances, ModuleScope};
use crate::ir::{DefId, DefLevels, ModuleId, Spec};
use crate::module::{Binding, Context, SymbolKind};
use crate::{Resolver, Result};

/// The first level error SANY reports, if any, and otherwise the levels of the definitions.
fn check(
    spec: &Spec,
    layout: &layout::Layout,
    scopes: &HashMap<ModuleId, ModuleScope>,
    kept: usize,
) -> std::result::Result<Vec<DefLevels>, Found> {
    let mut analyzer = Analyzer::new(spec, layout);
    analyzer.run();
    Instances::new(scopes).check(&mut analyzer);
    let errors = std::mem::take(&mut analyzer.errors);
    let first = errors
        .into_iter()
        .enumerate()
        .filter(|(_, error)| error.is_reported)
        .min_by_key(|(found, error)| (error.order, *found));
    if let Some((_, error)) = first {
        return Err(error);
    }
    Ok((0..kept).map(|index| analyzer.def_levels(DefId(index as u32))).collect())
}

impl Resolver<'_> {
    /// Computes the levels of the definitions and reports SANY's first level error.
    pub(crate) fn check_levels(&mut self) -> Result<()> {
        let defs = self.spec.defs.len();
        let constants = self.spec.constants.len();
        let variables = self.spec.variables.len();
        let assumptions = self.spec.assumptions.len();
        self.elaborate_standalone();
        let scopes = self.module_scopes();
        let checked = check(&self.spec, &self.layout, &scopes, defs);
        self.spec.defs.truncate(defs);
        self.spec.constants.truncate(constants);
        self.spec.variables.truncate(variables);
        self.spec.assumptions.truncate(assumptions);
        match checked {
            Ok(levels) => {
                self.spec.levels = levels;
                Ok(())
            }
            Err(found) => Err(self.error(found.module, found.span, found.message)),
        }
    }

    /// Elaborates by itself each module elaborated only under the substitutions of an `INSTANCE`,
    /// since SANY checks every module that way.
    fn elaborate_standalone(&mut self) {
        let mut failed = HashSet::new();
        loop {
            let mut pending: Vec<ModuleId> = self
                .instantiated
                .iter()
                .copied()
                .filter(|module| !self.plain.contains_key(module) && !failed.contains(module))
                .collect();
            if pending.is_empty() {
                break;
            }
            pending.sort();
            for module in pending {
                if self.standalone(module).is_err() {
                    failed.insert(module);
                }
            }
        }
    }

    fn standalone(&mut self, module: ModuleId) -> Result<()> {
        let name = self.spec.modules[module.index()].name;
        let parsed = self.parsed[&name].clone();
        // A nested module sees what the module around it defines before it, which a plain
        // elaboration of that module provides.
        if let (Some((_, false)), Some(&(parent, _))) =
            (self.enclosing.get(&module), self.inner_origins.get(&name))
        {
            self.plain.remove(&parent);
            self.standalone(parent)?;
        }
        self.plain(&parsed).map(|_| ())
    }

    /// What each module elaborated by itself defines and declares, leaving out what a nested
    /// module sees of the module around it.
    fn module_scopes(&self) -> HashMap<ModuleId, ModuleScope> {
        let mut scopes = HashMap::new();
        for (&module, context) in &self.plain {
            let enclosing = self.enclosing.get(&module).map(|(context, _)| context);
            let own = context.names.iter().filter(|(name, entry)| {
                let inherited = enclosing.and_then(|context| context.names.get(*name));
                inherited.is_none_or(|inherited| inherited.origin != entry.origin)
            });
            let mut scope = ModuleScope::default();
            let mut defs = BTreeSet::new();
            for (&name, entry) in own {
                match (entry.kind, &entry.binding) {
                    (SymbolKind::Operator, Binding::Def(def)) => {
                        defs.insert(*def);
                    }
                    (_, Binding::Instance(info)) => collect_members(&info.context, &mut defs),
                    (SymbolKind::Constant, Binding::Const(id)) => {
                        scope.declarations.push((name, Param::Const(*id)));
                    }
                    (SymbolKind::Variable, Binding::Var(id)) => {
                        scope.declarations.push((name, Param::Var(*id)));
                        scope.has_variables = true;
                    }
                    _ => {}
                }
            }
            scope.declarations.sort_by_key(|(_, param)| *param);
            scope.defs = defs.into_iter().collect();
            scope.assumptions = self
                .spec
                .assumptions
                .iter()
                .copied()
                .filter(|def| {
                    self.spec.def(*def).module == module
                        && !self.layout.defs[def.index()].is_instantiated
                })
                .collect();
            scopes.insert(module, scope);
        }
        scopes
    }
}

/// The definitions of a named instance, which SANY's module has as `I!Op`.
fn collect_members(context: &Context, defs: &mut BTreeSet<DefId>) {
    for entry in context.names.values().filter(|entry| !entry.is_local) {
        match &entry.binding {
            Binding::Def(def) if entry.kind == SymbolKind::Operator => {
                defs.insert(*def);
            }
            Binding::Instance(info) => collect_members(&info.context, defs),
            _ => {}
        }
    }
}

/// The span from the start of `first` to the end of `last`.
pub(crate) fn join(first: Span, last: Span) -> Span {
    Span { start: first.start, end: last.end }
}
