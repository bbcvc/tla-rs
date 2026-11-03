//! The constant definitions TLC computes once, as its `processConstantDefns` does, ported from
//! tla-ts `isConstantLevel`, `evaluateDefinitionValue`, `evaluateStartupDefinitions`, and
//! `toStartupValue`.
//!
//! A definition without parameters at the top level of a module is constant when its level is
//! constant and it doesn't use, itself or through another definition, an operator TLC counts as
//! state-level, such as `TLCGet` or `RandomSubset`. TLC computes it with its startup random
//! generator, once, and keeps the value; a definition the configuration or a native replaces
//! isn't computed. TLC computes them all when it starts, and ignores those that fail, which it
//! computes again where the spec uses them.

use tla_resolve::{Builtin, DefBody, DefId, Expr, ExprKind, Level, OpRef, Spec};
use tla_value::Value;

use super::analysis::for_each_child;
use crate::env::StateRef;
use crate::{Evaluator, Result};

/// Whether each definition, by [`DefId`], is a constant definition TLC computes once.
pub(crate) fn constant_definitions(spec: &Spec) -> Vec<bool> {
    let mut analysis = Analysis { spec, uses_state_level: vec![None; spec.defs.len()] };
    (0..spec.defs.len())
        .map(|index| {
            let id = DefId(index as u32);
            let def = spec.def(id);
            def.depth == 0
                && def.params.is_empty()
                && spec.level(id) == Level::Constant
                && !analysis.uses_state_level(id)
        })
        .collect()
}

struct Analysis<'a> {
    spec: &'a Spec,
    uses_state_level: Vec<Option<bool>>,
}

impl Analysis<'_> {
    /// Whether a definition is an operator TLC counts as state-level, or uses one, or reads a
    /// variable or the next state.
    fn uses_state_level(&mut self, id: DefId) -> bool {
        if let Some(known) = self.uses_state_level[id.index()] {
            return known;
        }
        // A definition that refers to itself counts as constant meanwhile, as in tla-ts.
        self.uses_state_level[id.index()] = Some(false);
        let spec = self.spec;
        let def = spec.def(id);
        let module = spec.modules[def.module.index()].name.as_str();
        let mut pending: Vec<&Expr> = match &def.body {
            DefBody::Expr(body) => vec![body],
            DefBody::Function { bounds, body } => {
                bounds.iter().map(|bound| &bound.set).chain([body]).collect()
            }
        };
        let mut found = crate::stdlib::is_state_level(module, def.name.as_str());
        while let Some(expr) = pending.pop() {
            if found {
                break;
            }
            match &expr.kind {
                ExprKind::Call { def, .. } | ExprKind::OpArg(OpRef::Def { def, .. }) => {
                    found = self.uses_state_level(*def);
                }
                // SANY's level skips an argument its operator ignores, as TLC's Naturals ignores
                // those of `*`, but the definition still reads what the argument reads.
                ExprKind::Var(_)
                | ExprKind::Builtin {
                    op: Builtin::Prime | Builtin::Unchanged | Builtin::Enabled,
                    ..
                } => found = true,
                _ => {}
            }
            for_each_child(expr, &mut |child| pending.push(child));
        }
        self.uses_state_level[id.index()] = Some(found);
        found
    }
}

impl Evaluator {
    /// The value of a constant definition, computed as TLC starts.
    pub(super) fn constant_value(&self, def: DefId) -> Result<Value> {
        self.constant_value_in(def, None, None)
    }

    /// The value of a constant definition, computed once with TLC's startup random generator.
    /// TLC goes on without one that fails as it starts, and computes it where the spec uses it,
    /// keeping it once that succeeds, as tla-ts does.
    pub(super) fn constant_value_in(
        &self,
        def: DefId,
        state: Option<StateRef<'_>>,
        next: Option<StateRef<'_>>,
    ) -> Result<Value> {
        let cell = &self.constant_values[def.index()];
        if let Some(value) = cell.get() {
            return Ok(value.clone());
        }
        let value = self
            .runtime
            .at_startup(|| self.enter(def, None, Vec::new(), state, next, Default::default()))?;
        let value = self.startup_value(def, value);
        Ok(cell.get_or_init(|| value).clone())
    }

    /// TLC computes a constant definition without keeping a function it constructs lazy, so a
    /// function over an interval or an enumerated set is enumerated.
    fn startup_value(&self, def: DefId, value: Value) -> Value {
        let is_function = matches!(self.spec.def(def).body, DefBody::Function { .. });
        if !is_function || self.is_recursive[def.index()] {
            return value;
        }
        match &value {
            Value::LazyFunc(lazy)
                if matches!(
                    lazy.domain,
                    Value::Set(_) | Value::MixedSet(_) | Value::Interval(..)
                ) =>
            {
                value.materialize().unwrap_or(value)
            }
            _ => value,
        }
    }

    /// Whether `def` is a constant definition the evaluator computes once, rather than replaced
    /// by the configuration or a native.
    pub(super) fn is_computed_once(&self, def: DefId) -> bool {
        self.is_constant_definition[def.index()]
            && self.overrides[def.index()].is_none()
            && self.natives[def.index()].is_none()
    }

    /// Computes the constant definitions, as TLC does when it starts, before it checks the
    /// assumptions. A definition that fails is left to compute where the spec uses it.
    ///
    /// TLC goes through the modules in the order SANY finishes them, and through a module's
    /// definitions in the order of SANY's symbol table; this goes through them in the order the
    /// resolver numbers them.
    pub fn evaluate_constant_definitions(&self) {
        for index in 0..self.spec.defs.len() {
            let def = DefId(index as u32);
            if self.is_computed_once(def) {
                let _ = self.constant_value(def);
            }
        }
    }
}

#[cfg(test)]
mod tests;
