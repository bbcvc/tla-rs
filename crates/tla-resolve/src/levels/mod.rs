//! SANY's level checking: the level of every definition, and the level errors SANY reports.
//!
//! An expression's level is what it can mention: constants, unprimed variables, primed variables,
//! or temporal operators. SANY computes the level of every definition, with the highest level each
//! parameter allows and the lowest level each operator parameter requires, and rejects
//! expressions TLA+ forbids, such as `[]A` for an action `A`, or an argument above the level its
//! operator allows. The pass follows tla-ts `levels.ts` and `sany/levels.ts`, which port SANY's
//! `levelCheck` methods.
//!
//! The levels of a definition come from its resolved body. Resolution copies the definitions of
//! an instantiated module with the substitutions in place, so their levels are those of the
//! substituted bodies. SANY instead checks each module once by itself, so errors are only
//! reported in modules resolution elaborated by themselves.

mod analyzer;
mod data;
mod expr;
pub(crate) mod layout;
mod leibniz;

use self::analyzer::{Analyzer, Found};
use crate::ir::{DefId, DefLevels, Spec};
use crate::{Resolver, Result};

/// The first level error SANY reports, if any, and otherwise the levels of the definitions.
fn check(spec: &Spec, layout: &layout::Layout) -> std::result::Result<Vec<DefLevels>, Found> {
    let mut analyzer = Analyzer::new(spec, layout);
    analyzer.run();
    let errors = std::mem::take(&mut analyzer.errors);
    let reported = errors.into_iter().enumerate().filter(|(_, error)| error.is_reported);
    if let Some((_, error)) = reported.min_by_key(|(found, error)| (error.order, *found)) {
        return Err(error);
    }
    Ok((0..spec.defs.len()).map(|index| analyzer.def_levels(DefId(index as u32))).collect())
}

impl Resolver<'_> {
    /// Computes the levels of the definitions and reports SANY's first level error.
    pub(crate) fn check_levels(&mut self) -> Result<()> {
        match check(&self.spec, &self.layout) {
            Ok(levels) => {
                self.spec.levels = levels;
                Ok(())
            }
            Err(found) => Err(self.error(found.module, found.span, found.message)),
        }
    }
}
