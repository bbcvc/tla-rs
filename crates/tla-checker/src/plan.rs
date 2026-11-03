//! Spec processing, as TLC's `SpecProcessor` and tla-ts `search.ts` do it: what the model
//! configuration asks the model checker to explore and check.
//!
//! A `SPECIFICATION` splits into the conjuncts of its initial predicate, one `[][Next]_v`, and
//! temporal formulas such as fairness, which liveness checking reads. A `PROPERTY` splits the
//! same way: `[]P` with a state predicate `P` is checked like an invariant, `[][A]_v` on every
//! step, a state predicate on the initial states, and the rest is left to liveness. The model
//! checker takes zero-arity definitions, so each part that isn't one becomes a definition of its
//! own, beside the definition it comes from.

use std::collections::HashMap;

use tla_parser::ModelConfig;
use tla_resolve::{Builtin, DefBody, DefId, Expr, ExprKind, Level, RootName, Scope, Spec};
use tla_value::Symbol;

use crate::Error;
use crate::level::{Levels, STATE_LEVEL_OPERATORS};
use crate::liveness::template::Template;
pub use parts::describe_range;
use parts::{Part, always, is_temporal_quantifier};

mod parts;
mod temporal;

/// A named predicate the model checker evaluates.
#[derive(Clone, Debug)]
pub struct Check {
    /// The name TLC reports when the check fails.
    pub name: String,
    pub def: DefId,
}

/// What the model checker explores and checks.
#[derive(Clone, Debug, Default)]
pub struct Plan {
    /// The conjuncts of the initial predicate.
    pub init: Vec<DefId>,
    /// `Next` of `[][Next]_v`.
    pub next: Option<DefId>,
    /// Checked on every state, the initial ones included.
    pub invariants: Vec<Check>,
    /// State predicates of properties, which hold of the initial states.
    pub initial_predicates: Vec<Check>,
    /// `[A]_v` of the property `[][A]_v`, which holds of every step.
    pub action_properties: Vec<Check>,
    /// The temporal parts of the properties, by name, which liveness checking checks.
    pub properties: Vec<(String, Template)>,
    /// The temporal parts of the specification, such as fairness, which liveness checking
    /// assumes of every behavior.
    pub fairness: Vec<Template>,
    pub constraints: Vec<Check>,
    pub action_constraints: Vec<Check>,
    /// The `VIEW`, whose value tells states apart instead of their variables.
    pub view: Option<DefId>,
    /// The `_POSSIBLE` state predicates, each of which some state of the model must satisfy.
    pub possible: Vec<Check>,
    /// The `_POSSIBLE` actions, each of which some step of the model must satisfy.
    pub action_possible: Vec<Check>,
    /// The `POSTCONDITION`s, checked once the search ends.
    pub postconditions: Vec<Postcondition>,
    /// Constant-level parts whose value decides whether they are checked, which the model
    /// checker evaluates before it starts.
    pub constants: Vec<Constant>,
}

impl Plan {
    /// Whether the plan checks anything of behaviors, so that it needs a next-state relation.
    pub fn checks_behaviors(&self) -> bool {
        !self.invariants.is_empty()
            || !self.action_properties.is_empty()
            || !self.properties.is_empty()
    }
}

/// A postcondition the configuration names.
#[derive(Clone, Debug)]
pub struct Postcondition {
    pub name: String,
    /// The zero-arity definition the name refers to, if any.
    pub def: Option<DefId>,
    /// Whether TLC computes the definition when it starts, so that it rejects it.
    pub is_constant: bool,
}

/// A constant-level part of the configuration or a formula, which TLC evaluates as it processes
/// the spec.
#[derive(Clone, Debug)]
pub struct Constant {
    pub def: DefId,
    pub usage: Usage,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Usage {
    /// A conjunct of the specification or of a property, which must be `TRUE`.
    Conjunct { name: String, is_spec: bool },
    /// An invariant, constraint, or property the configuration names, which isn't checked when
    /// it is `TRUE`.
    Predicate { kind: &'static str, name: String },
    /// The initial predicate or next-state action, which can't be a constant.
    Operator { kind: &'static str, name: String },
}

/// Processes the configuration against `spec`, adding the definitions the parts need to it.
/// `overrides` are the definitions the configuration replaces with other definitions.
pub fn plan(
    spec: &mut Spec,
    config: &ModelConfig,
    overrides: &HashMap<DefId, DefId>,
) -> Result<Plan, Error> {
    let mut planner = Planner {
        spec,
        overrides,
        plan: Plan::default(),
        levels: Levels::tlc(),
        sany: Levels::sany(STATE_LEVEL_OPERATORS),
        temporal_properties: Vec::new(),
        temporal_spec: Vec::new(),
    };
    planner.invariants(&config.invariants)?;
    planner.specification(config)?;
    planner.properties(&config.properties)?;
    let has_variables = !planner.spec.variables.is_empty();
    let checks_behaviors =
        planner.plan.checks_behaviors() || !planner.temporal_properties.is_empty();
    let plan = &planner.plan;
    if plan.init.is_empty()
        && config.specification.is_none()
        && config.init.is_none()
        && (checks_behaviors || !plan.initial_predicates.is_empty() || has_variables)
    {
        return Err(Error::config(
            "The configuration file did not specify the initial state predicate.",
        ));
    }
    if plan.next.is_none() && checks_behaviors {
        return Err(Error::config(
            "The configuration file did not specify the next state predicate.",
        ));
    }
    planner.plan.constraints = planner.predicates("constraint", &config.constraints)?;
    planner.plan.action_constraints =
        planner.predicates("action constraint", &config.action_constraints)?;
    for (kind, name) in [("rlreward", config.rl_reward), ("periodic", config.periodic)] {
        if let Some(name) = name {
            planner.operator(kind, name)?;
        }
    }
    planner.possible(&config.possible)?;
    if let Some(view) = config.view {
        planner.plan.view = Some(planner.operator("view function", view)?);
    }
    planner.postconditions(&config.postconditions);
    // TLC builds the liveness checker, and so translates the temporal formulas, only when
    // there are temporal properties to check.
    if !planner.temporal_properties.is_empty() {
        for (name, part) in std::mem::take(&mut planner.temporal_properties) {
            let template = planner.temporal(&part)?;
            planner.plan.properties.push((name, template));
        }
        for part in std::mem::take(&mut planner.temporal_spec) {
            let template = planner.temporal(&part)?;
            planner.plan.fairness.push(template);
        }
    }
    Ok(planner.plan)
}

struct Planner<'s> {
    spec: &'s mut Spec,
    overrides: &'s HashMap<DefId, DefId>,
    plan: Plan,
    /// TLC's level bound, which sorts the parts of formulas and finds constants.
    levels: Levels,
    /// SANY's levels, by which TLC checks invariants and computes constant definitions.
    sany: Levels,
    /// The temporal parts of the properties and of the specification, translated once the
    /// configuration is processed.
    temporal_properties: Vec<(String, Part)>,
    temporal_spec: Vec<Part>,
}

impl Planner<'_> {
    /// The zero-arity definition a configuration names.
    fn operator(&self, kind: &'static str, name: Symbol) -> Result<DefId, Error> {
        let def = match self.spec.lookup(name.as_str()) {
            Some(RootName::Def(def)) => def,
            _ => {
                return Err(Error::config(format!(
                    "The {kind} {name} specified in the configuration file\nis not defined in the specification."
                )));
            }
        };
        if !self.spec.def(def).params.is_empty() {
            return Err(Error::config(match kind {
                "name" | "property" => format!("TLC requires {name} not to take any argument."),
                _ => format!(
                    "TLC requires {kind} not to take any argument, but one was given: {name}"
                ),
            }));
        }
        Ok(*self.overrides.get(&def).unwrap_or(&def))
    }

    /// The predicates the configuration names. A constant the configuration assigns `TRUE`
    /// is no check.
    fn predicates(&mut self, kind: &'static str, names: &[Symbol]) -> Result<Vec<Check>, Error> {
        let mut checks = Vec::new();
        for &name in names {
            if let Some(RootName::Const(_)) = self.spec.lookup(name.as_str()) {
                // bind_model has checked the value.
                continue;
            }
            let def = self.operator(kind, name)?;
            if self.def_level(def) == Level::Constant {
                let usage = Usage::Predicate { kind, name: name.to_string() };
                self.plan.constants.push(Constant { def, usage });
            }
            checks.push(Check { name: name.to_string(), def });
        }
        Ok(checks)
    }

    fn invariants(&mut self, names: &[Symbol]) -> Result<(), Error> {
        for check in self.predicates("invariant", names)? {
            if self.sany.def_level(self.spec, check.def) >= Level::Action {
                return Err(Error::config(format!(
                    "The invariant {} is not a state predicate (one with no primes or temporal operators).",
                    check.name
                )));
            }
            self.plan.invariants.push(check);
        }
        Ok(())
    }

    /// The `_POSSIBLE` predicates, sorted into those of states and those of steps.
    fn possible(&mut self, names: &[Symbol]) -> Result<(), Error> {
        for (index, &name) in names.iter().enumerate() {
            if names[..index].contains(&name) {
                return Err(Error::config(format!("_POSSIBLE lists {name} more than once")));
            }
            let def = self.operator("possible", name)?;
            self.constant_operator("possible", name, def);
            let check = Check { name: name.to_string(), def };
            match self.def_level(def) {
                Level::Temporal => {
                    return Err(Error::config(format!(
                        "The possible of {name} is equal to a temporal formula; only state- and action-level predicates are supported"
                    )));
                }
                Level::Action => self.plan.action_possible.push(check),
                _ => self.plan.possible.push(check),
            }
        }
        Ok(())
    }

    /// The postconditions, which TLC looks up only once the search ends.
    fn postconditions(&mut self, names: &[Symbol]) {
        for &name in names {
            let def = match self.spec.lookup(name.as_str()) {
                Some(RootName::Def(def)) if self.spec.def(def).params.is_empty() => Some(def),
                _ => None,
            };
            let is_constant = def.is_some_and(|def| {
                self.spec.def(def).depth == 0
                    && self.sany.def_level(self.spec, def) == Level::Constant
            });
            self.plan.postconditions.push(Postcondition {
                name: name.to_string(),
                def,
                is_constant,
            });
        }
    }

    fn def_level(&self, def: DefId) -> Level {
        self.levels.def_level(self.spec, def)
    }

    fn level(&self, expr: &Expr) -> Level {
        self.levels.level(self.spec, expr)
    }

    fn specification(&mut self, config: &ModelConfig) -> Result<(), Error> {
        let Some(name) = config.specification else {
            if let Some(init) = config.init {
                let def = self.operator("initial predicate", init)?;
                self.constant_operator("initial predicate", init, def);
                self.plan.init.push(def);
            }
            if let Some(next) = config.next {
                let def = self.operator("next state action", next)?;
                self.constant_operator("next state action", next, def);
                self.plan.next = Some(def);
            }
            return Ok(());
        };
        if config.init.is_some() || config.next.is_some() {
            return Err(Error::config(
                "The configuration file cannot specify both INIT/NEXT and SPECIFICATION fields.",
            ));
        }
        let def = self.operator("name", name)?;
        let mut parts = Vec::new();
        let part = Part {
            owner: def,
            expr: Self::body(self.spec, def),
            name: name.to_string(),
            via: None,
        };
        self.expand(part, &mut parts, &mut Vec::new())?;
        let mut init = Vec::new();
        let mut next = Vec::new();
        for part in parts {
            if self.is_constant_conjunct(&part, true) {
                continue;
            }
            let expr = &part.expr;
            if is_temporal_quantifier(expr) {
                return Err(Error::config(
                    "TLC does not support temporal existential, nor universal, quantification over state variables.",
                ));
            }
            if let Some(operand) = always(expr) {
                if let ExprKind::BoxAction { action, .. } = &operand.kind {
                    next.push(self.part_def(&part, action));
                    continue;
                }
                if self.part_level(part.via.as_ref(), operand) < Level::Action {
                    return Err(Error::config(format!(
                        "TLC cannot handle the temporal formula {}",
                        self.describe(part.owner, operand.span)
                    )));
                }
            }
            match self.part_level(part.via.as_ref(), expr) {
                Level::Temporal => self.temporal_spec.push(part),
                Level::Action => {
                    return Err(Error::config(format!(
                        "TLC cannot handle the action-level conjunct of the specification {name}"
                    )));
                }
                _ => init.push(self.part_def(&part, expr)),
            }
        }
        if next.len() > 1 {
            return Err(Error::config(format!(
                "The specification {name} must contain at most one [][Next]_vars"
            )));
        }
        self.plan.init = init;
        self.plan.next = next.pop();
        Ok(())
    }

    fn properties(&mut self, names: &[Symbol]) -> Result<(), Error> {
        for &name in names {
            if let Some(RootName::Const(_)) = self.spec.lookup(name.as_str()) {
                continue;
            }
            let def = self.operator("property", name)?;
            // TLC evaluates a constant property as it processes the spec, and doesn't check one
            // that is true. One that fails to evaluate is checked on the initial states.
            if self.def_level(def) == Level::Constant {
                let usage = Usage::Predicate { kind: "property", name: name.to_string() };
                self.plan.constants.push(Constant { def, usage });
                self.plan.initial_predicates.push(Check { name: name.to_string(), def });
                continue;
            }
            let mut parts = Vec::new();
            let body = Self::body(self.spec, def);
            let part = Part { owner: def, expr: body, name: name.to_string(), via: None };
            self.expand(part, &mut parts, &mut Vec::new())?;
            for part in parts {
                if self.is_constant_conjunct(&part, false) {
                    continue;
                }
                let expr = &part.expr;
                if let Some(operand) = always(expr) {
                    if let ExprKind::BoxAction { action, sub } = &operand.kind {
                        // `[A]_v` holds of a step when `A` does or `v` doesn't change.
                        let unchanged = Expr::new(
                            ExprKind::Builtin {
                                op: Builtin::Unchanged,
                                args: vec![(**sub).clone()],
                            },
                            sub.span,
                        );
                        let step = Expr::new(
                            ExprKind::Or(vec![(**action).clone(), unchanged]),
                            operand.span,
                        );
                        let def = self.part_def(&part, &step);
                        self.plan.action_properties.push(Check { name: part.name, def });
                        continue;
                    }
                    if self.part_level(part.via.as_ref(), operand) <= Level::State {
                        // TLC names the invariant by the operator `[]` applies to, if any.
                        let name = match &operand.kind {
                            ExprKind::Call { def, args, .. } if args.is_empty() => {
                                self.spec.def(*def).name.to_string()
                            }
                            _ => part.name.clone(),
                        };
                        let def = self.part_def(&part, operand);
                        self.plan.invariants.push(Check { name, def });
                        continue;
                    }
                }
                match self.part_level(part.via.as_ref(), expr) {
                    Level::Constant | Level::State => {
                        let def = self.part_def(&part, expr);
                        self.plan.initial_predicates.push(Check { name: part.name, def });
                    }
                    Level::Action => {
                        return Err(Error::config(format!(
                            "The property {name} is an action-level formula"
                        )));
                    }
                    Level::Temporal => {
                        let name = part.name.clone();
                        self.temporal_properties.push((name, part));
                    }
                }
            }
        }
        Ok(())
    }

    /// Whether a part is a constant-level definition, which TLC evaluates and drops if it is
    /// `TRUE` and otherwise rejects.
    fn is_constant_conjunct(&mut self, part: &Part, is_spec: bool) -> bool {
        let ExprKind::Call { def, scope: Scope::Global, args } = &part.expr.kind else {
            return false;
        };
        if !args.is_empty() || self.level(&part.expr) > Level::Constant {
            return false;
        }
        let name = self.spec.def(*def).name.to_string();
        self.plan.constants.push(Constant { def: *def, usage: Usage::Conjunct { name, is_spec } });
        true
    }

    fn constant_operator(&mut self, kind: &'static str, name: Symbol, def: DefId) {
        let is_literal = matches!(
            &self.spec.def(def).body,
            DefBody::Expr(Expr { kind: ExprKind::Int(_) | ExprKind::Str(_), .. })
        );
        if self.def_level(def) == Level::Constant && !is_literal {
            let usage = Usage::Operator { kind, name: name.to_string() };
            self.plan.constants.push(Constant { def, usage });
        }
    }
}

#[cfg(test)]
mod tests;
