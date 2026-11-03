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

use tla_ast::{Quantifier, Span};
use tla_parser::ModelConfig;
use tla_resolve::{
    Builtin, Def, DefBody, DefId, DefLevels, Expr, ExprKind, Level, RootName, Scope, Spec,
};
use tla_value::Symbol;

use crate::Error;
use crate::level::Levels;

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
    /// The properties left to liveness checking, by name.
    pub liveness: Vec<String>,
    /// Temporal conjuncts of the specification, such as fairness.
    pub temporals: usize,
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
            || !self.liveness.is_empty()
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

/// One conjunct of a formula, in the definition whose frame its expression lives in.
struct Part {
    owner: DefId,
    expr: Expr,
    name: String,
    /// How a module-level definition reaches the frame of `owner`, when `owner` is a
    /// definition of a parameterized instance.
    via: Option<Via>,
}

/// A call of a definition of a parameterized instance, as in `I(y)!Spec`, from a module-level
/// definition.
#[derive(Clone)]
struct Via {
    /// The module-level definition the instance's arguments are written in.
    caller: DefId,
    scope: Scope,
}

/// Processes the configuration against `spec`, adding the definitions the parts need to it.
/// `overrides` are the definitions the configuration replaces with other definitions.
pub fn plan(
    spec: &mut Spec,
    config: &ModelConfig,
    overrides: &HashMap<DefId, DefId>,
) -> Result<Plan, Error> {
    let mut planner = Planner { spec, overrides, plan: Plan::default(), levels: Levels::default() };
    planner.invariants(&config.invariants)?;
    planner.specification(config)?;
    planner.properties(&config.properties)?;
    let has_variables = !planner.spec.variables.is_empty();
    let plan = &planner.plan;
    if plan.init.is_empty()
        && config.specification.is_none()
        && config.init.is_none()
        && (plan.checks_behaviors() || !plan.initial_predicates.is_empty() || has_variables)
    {
        return Err(Error::config(
            "The configuration file did not specify the initial state predicate.",
        ));
    }
    if plan.next.is_none() && plan.checks_behaviors() {
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
    Ok(planner.plan)
}

struct Planner<'s> {
    spec: &'s mut Spec,
    overrides: &'s HashMap<DefId, DefId>,
    plan: Plan,
    levels: Levels,
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
            if self.def_level(check.def) >= Level::Action {
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
                self.spec.def(def).depth == 0 && self.def_level(def) == Level::Constant
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
                Level::Temporal => self.plan.temporals += 1,
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
                    Level::Temporal => self.plan.liveness.push(name.to_string()),
                }
            }
        }
        Ok(())
    }

    fn body(spec: &Spec, def: DefId) -> Expr {
        match &spec.def(def).body {
            DefBody::Expr(expr) => expr.clone(),
            DefBody::Function { .. } => Expr::new(
                ExprKind::Call { def, scope: Scope::Global, args: Vec::new() },
                spec.def(def).span,
            ),
        }
    }

    /// Splits a formula into its conjuncts, following the zero-arity definitions it applies
    /// that aren't constants, as TLC's `Tool.processSpec` does, those of parameterized
    /// instances included.
    fn expand(
        &self,
        part: Part,
        parts: &mut Vec<Part>,
        expanding: &mut Vec<DefId>,
    ) -> Result<(), Error> {
        let Part { owner, expr, name, via } = part;
        // The definition the conjunct applies, and how its frame is reached.
        let (target, inner) = match &expr.kind {
            ExprKind::And(items) => {
                for item in items {
                    let name = self.describe(owner, item.span);
                    let part = Part { owner, expr: item.clone(), name, via: via.clone() };
                    self.expand(part, parts, expanding)?;
                }
                return Ok(());
            }
            ExprKind::Call { def, scope: Scope::Global, args } if args.is_empty() => {
                (*self.overrides.get(def).unwrap_or(def), None)
            }
            // A definition of the parameterized instance `owner` belongs to, in its frame.
            ExprKind::Call { def, scope: Scope::Up(_), args }
                if args.is_empty()
                    && via.is_some()
                    && self.spec.def(*def).depth == self.spec.def(owner).depth =>
            {
                (*def, via.clone())
            }
            ExprKind::Call { def, scope: scope @ Scope::Instance { parent, .. }, args }
                if args.is_empty()
                    && via.is_none()
                    && **parent == Scope::Global
                    && self.spec.def(owner).depth == 0 =>
            {
                (*def, Some(Via { caller: owner, scope: scope.clone() }))
            }
            _ => {
                parts.push(Part { owner, expr, name, via });
                return Ok(());
            }
        };
        let callee = self.spec.def(target);
        let is_expandable = callee.params.is_empty()
            && matches!(callee.body, DefBody::Expr(_))
            && (callee.depth == 0 || inner.is_some())
            && self.part_level(via.as_ref(), &expr) > Level::Constant;
        if !is_expandable {
            parts.push(Part { owner, expr, name, via });
            return Ok(());
        }
        if expanding.contains(&target) {
            return Err(Error::config("Stack overflow while processing the specification."));
        }
        expanding.push(target);
        let body = Self::body(self.spec, target);
        let part = Part { owner: target, expr: body, name: callee.name.to_string(), via: inner };
        let result = self.expand(part, parts, expanding);
        expanding.pop();
        result
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

    /// The level of `expr` in a frame `via` reaches, with the arguments of the instance.
    fn part_level(&self, via: Option<&Via>, expr: &Expr) -> Level {
        let level = self.level(expr);
        match via {
            Some(Via { scope: Scope::Instance { args, .. }, .. }) => {
                args.iter().map(|arg| self.level(arg)).fold(level, Level::max)
            }
            _ => level,
        }
    }

    /// A zero-arity module-level definition for `expr` in the frame of `part`: the definition
    /// `expr` applies if it is a plain reference to one, and otherwise a new one.
    fn part_def(&mut self, part: &Part, expr: &Expr) -> DefId {
        if let ExprKind::Call { def, scope: Scope::Global, args } = &expr.kind
            && args.is_empty()
            && self.spec.def(*def).params.is_empty()
        {
            return *self.overrides.get(def).unwrap_or(def);
        }
        let level = self.part_level(part.via.as_ref(), expr);
        let def = self.new_def(part.owner, expr.clone(), &part.name, level);
        match &part.via {
            None => def,
            // A definition in the instance's frame, which a module-level one calls.
            Some(Via { caller, scope }) => {
                let call = ExprKind::Call { def, scope: scope.clone(), args: Vec::new() };
                self.new_def(*caller, Expr::new(call, expr.span), &part.name, level)
            }
        }
    }

    /// A new zero-arity definition with `body`, in the frame of `owner`.
    fn new_def(&mut self, owner: DefId, body: Expr, name: &str, level: Level) -> DefId {
        let owner = self.spec.def(owner);
        let def = Def {
            name: Symbol::intern(name),
            module: owner.module,
            span: body.span,
            params: Vec::new(),
            body: DefBody::Expr(body),
            frame_size: owner.frame_size,
            depth: owner.depth,
            is_instantiated: owner.is_instantiated,
        };
        self.spec.defs.push(def);
        self.spec.levels.push(DefLevels {
            level,
            max_levels: Vec::new(),
            weights: Vec::new(),
            min_max_levels: Vec::new(),
            leibniz: Vec::new(),
        });
        DefId(self.spec.defs.len() as u32 - 1)
    }

    /// TLC's description of a range: `line 3, col 6 to line 3, col 14 of module M`.
    fn describe(&self, owner: DefId, span: Span) -> String {
        describe_range(self.spec, self.spec.def(owner).module, span)
    }
}

/// TLC's description of a range of a module.
pub fn describe_range(spec: &Spec, module: tla_resolve::ModuleId, span: Span) -> String {
    let info = &spec.modules[module.index()];
    let (line, column) = span.line_column(&info.source);
    let last = Span::new(span.end.saturating_sub(1).max(span.start) as usize, span.end as usize);
    let (end_line, end_column) = last.line_column(&info.source);
    format!(
        "line {line}, col {column} to line {end_line}, col {end_column} of module {}",
        info.name
    )
}

/// The operand of `[]`, if the expression applies it.
fn always(expr: &Expr) -> Option<&Expr> {
    match &expr.kind {
        ExprKind::Builtin { op: Builtin::Always, args } => args.first(),
        _ => None,
    }
}

fn is_temporal_quantifier(expr: &Expr) -> bool {
    matches!(
        &expr.kind,
        ExprKind::UnboundedQuant {
            quantifier: Quantifier::TemporalExists | Quantifier::TemporalForall,
            ..
        }
    )
}

#[cfg(test)]
mod tests;
