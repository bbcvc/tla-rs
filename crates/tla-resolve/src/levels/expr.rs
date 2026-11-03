//! The level information of resolved expressions, by the rules of SANY's built-in operators and
//! tla-ts `analyzeNode`, and the level errors SANY reports in them.

use std::rc::Rc;

use tla_ast::{Fairness, Quantifier, Span};

use super::analyzer::{Analyzer, Body};
use super::data::{Data, Operand, Operator, Param, apply, apply_declared};
use crate::ir::{Bound, Builtin, DefId, ExceptKey, Expr, ExprKind, Level, OpRef, Pattern, Scope};

/// SANY's name for a built-in operator.
fn builtin_name(op: Builtin) -> &'static str {
    match op {
        Builtin::Boolean => "BOOLEAN",
        Builtin::String => "STRING",
        Builtin::And => "\\land",
        Builtin::Or => "\\lor",
        Builtin::Eq => "=",
        Builtin::Neq => "/=",
        Builtin::Not => "\\lnot",
        Builtin::Implies => "=>",
        Builtin::Equiv => "\\equiv",
        Builtin::In => "\\in",
        Builtin::NotIn => "\\notin",
        Builtin::SubsetEq => "\\subseteq",
        Builtin::Cup => "\\union",
        Builtin::Cap => "\\intersect",
        Builtin::SetMinus => "\\",
        Builtin::Powerset => "SUBSET",
        Builtin::Union => "UNION",
        Builtin::Domain => "DOMAIN",
        Builtin::Prime => "'",
        Builtin::Unchanged => "UNCHANGED",
        Builtin::Enabled => "ENABLED",
        Builtin::Always => "[]",
        Builtin::Eventually => "<>",
        Builtin::LeadsTo => "~>",
        Builtin::PlusArrow => "-+->",
        Builtin::Cdot => "\\cdot",
    }
}

fn pattern_slots(pattern: &Pattern) -> &[usize] {
    match pattern {
        Pattern::Names(slots) | Pattern::Tuple(slots) => slots,
    }
}

impl Analyzer<'_> {
    pub(super) fn expr(&mut self, body: &Body, expr: &Expr) -> Data {
        let span = expr.span;
        match &expr.kind {
            ExprKind::Bool(_) | ExprKind::Int(_) | ExprKind::Str(_) => Data::default(),
            ExprKind::Var(id) => apply_declared(Param::Var(*id), Level::State, &[]),
            ExprKind::Const(id) => apply_declared(Param::Const(*id), Level::Constant, &[]),
            ExprKind::Local(local) => apply_declared(body.param(*local), Level::Constant, &[]),
            ExprKind::Call { def, scope, args } => {
                let (operator, instance_args) = self.callee(*def, scope);
                let mut operands = self.operands(body, &instance_args);
                operands.extend(self.operands(body, args));
                self.apply_operator(body, span, &operator, &operands, &[], &[])
            }
            ExprKind::CallParam { param, args } => {
                let operands = self.operands(body, args);
                apply_declared(body.param(*param), Level::Constant, &operands)
            }
            ExprKind::CallConst { id, args } => {
                let operands = self.operands(body, args);
                apply_declared(Param::Const(*id), Level::Constant, &operands)
            }
            ExprKind::Builtin { op, args } => self.builtin_application(body, expr, *op, args),
            ExprKind::OpArg(_) => self.operand(body, expr).data,
            ExprKind::And(items) | ExprKind::Or(items) => {
                let is_and = matches!(expr.kind, ExprKind::And(_));
                let operands = self.operands(body, items);
                let name = if is_and { "$ConjList" } else { "$DisjList" };
                let data = self.apply_builtin(body, span, name, &operands, &[], &[]);
                let logical = match (is_and, self.is_bulleted(body, span)) {
                    (true, true) => "Conjunction list",
                    (true, false) => "\\land",
                    (false, true) => "Disjunction list",
                    (false, false) => "\\lor",
                };
                self.check_junction(body, span, logical, &operands);
                data
            }
            ExprKind::If { cond, then, otherwise } => {
                let items = [&**cond, &**then, &**otherwise];
                let operands = items.map(|item| self.operand(body, item));
                self.apply_builtin(body, span, "$IfThenElse", &operands, &[], &[])
            }
            ExprKind::Case { arms, other } => {
                let mut items: Vec<&Expr> =
                    arms.iter().flat_map(|(guard, arm)| [guard, arm]).collect();
                items.extend(other.as_deref());
                let operands = self.operands(body, &items);
                self.apply_builtin(body, span, "$Case", &operands, &[], &[])
            }
            ExprKind::Quant { quantifier, bounds, body: predicate } => {
                let name = match quantifier {
                    Quantifier::Forall => "$BoundedForall",
                    _ => "$BoundedExists",
                };
                let (data, range_levels) = self.binding(body, span, name, predicate, bounds);
                if data.level == Level::Temporal {
                    let mut levels = bounds.iter().zip(range_levels);
                    if let Some((bound, _)) = levels.find(|(_, level)| *level == Level::Action) {
                        let message = "Action-level bound of quantified temporal formula.";
                        self.error(body.def, bound.set.span, message);
                    }
                }
                data
            }
            ExprKind::UnboundedQuant { quantifier, slots, body: predicate } => {
                let name = match quantifier {
                    Quantifier::Forall => "$UnboundedForall",
                    Quantifier::Exists => "$UnboundedExists",
                    Quantifier::TemporalForall => "$TemporalForall",
                    Quantifier::TemporalExists => "$TemporalExists",
                };
                let operands = [self.operand(body, predicate)];
                let bound: Vec<Param> = slots.iter().map(|&slot| body.slot(slot)).collect();
                self.apply_builtin(body, span, name, &operands, &[], &bound)
            }
            ExprKind::Choose { pattern, set, body: predicate } => {
                let ranges: Vec<Data> = set.iter().map(|set| self.expr(body, set)).collect();
                let bound: Vec<Param> =
                    pattern_slots(pattern).iter().map(|&slot| body.slot(slot)).collect();
                let name = if set.is_some() { "$BoundedChoose" } else { "$UnboundedChoose" };
                let operands = [self.operand(body, predicate)];
                self.apply_builtin(body, span, name, &operands, &ranges, &bound)
            }
            ExprKind::SetEnum(items) => self.apply_items(body, span, "$SetEnumerate", items),
            ExprKind::Tuple(items) => self.apply_items(body, span, "$Tuple", items),
            ExprKind::Product(items) => self.apply_items(body, span, "$CartesianProd", items),
            ExprKind::FuncSet { domain, range } => {
                let operands = [self.operand(body, domain), self.operand(body, range)];
                self.apply_builtin(body, span, "$SetOfFcns", &operands, &[], &[])
            }
            ExprKind::SetFilter { bound, pred } => {
                self.binding(body, span, "$SubsetOf", pred, std::slice::from_ref(&**bound)).0
            }
            ExprKind::SetMap { body: element, bounds } => {
                self.binding(body, span, "$SetOfAll", element, bounds).0
            }
            ExprKind::Function { bounds, body: value } => self.function(body, span, bounds, value),
            ExprKind::Record(fields) => {
                let values: Vec<&Expr> = fields.iter().map(|(_, value)| value).collect();
                let operands = self.operands(body, &values);
                self.apply_builtin(body, span, "$RcdConstructor", &operands, &[], &[])
            }
            ExprKind::RecordSet(fields) => {
                let values: Vec<&Expr> = fields.iter().map(|(_, value)| value).collect();
                let operands = self.operands(body, &values);
                self.apply_builtin(body, span, "$SetOfRcds", &operands, &[], &[])
            }
            ExprKind::FuncApp { func, args } => {
                let argument = match args.as_slice() {
                    [arg] => self.operand(body, arg),
                    _ => Operand::value(self.apply_items(body, span, "$Tuple", args)),
                };
                let operands = [self.operand(body, func), argument];
                self.apply_builtin(body, span, "$FcnApply", &operands, &[], &[])
            }
            ExprKind::Dot { record, .. } => {
                let operands = [self.operand(body, record), Operand::default()];
                self.apply_builtin(body, span, "$RcdSelect", &operands, &[], &[])
            }
            ExprKind::Except { base, updates } => {
                let mut operands = vec![self.operand(body, base)];
                let mut at_slots = Vec::new();
                for update in updates {
                    for key in &update.path {
                        if let ExceptKey::Apply(args) = key {
                            operands.extend(self.operands(body, args));
                        }
                    }
                    operands.push(self.operand(body, &update.value));
                    at_slots.push(body.slot(update.at));
                }
                // `@` is a constant to SANY, so it constrains nothing.
                self.apply_builtin(body, span, "$Except", &operands, &[], &at_slots)
            }
            ExprKind::BoxAction { action, sub } | ExprKind::AngleAction { action, sub } => {
                let name = match expr.kind {
                    ExprKind::BoxAction { .. } => "$SquareAct",
                    _ => "$AngleAct",
                };
                let operands = [self.operand(body, action), self.operand(body, sub)];
                self.apply_builtin(body, span, name, &operands, &[], &[])
            }
            ExprKind::Fairness { fairness, sub, action } => {
                let name = match fairness {
                    Fairness::Weak => "$WF",
                    Fairness::Strong => "$SF",
                };
                let operands = [self.operand(body, sub), self.operand(body, action)];
                self.apply_builtin(body, span, name, &operands, &[], &[])
            }
        }
    }

    /// `f[x \in S] == body`, or `[x \in S |-> body]`.
    pub(super) fn function(
        &mut self,
        body: &Body,
        span: Span,
        bounds: &[Bound],
        value: &Expr,
    ) -> Data {
        self.binding(body, span, "$FcnConstructor", value, bounds).0
    }

    /// An operator that binds variables to elements of the sets of `bounds` in `operand`. Returns
    /// the level information of the application and the level of each set.
    fn binding(
        &mut self,
        body: &Body,
        span: Span,
        name: &'static str,
        operand: &Expr,
        bounds: &[Bound],
    ) -> (Data, Vec<Level>) {
        let ranges: Vec<Data> = bounds.iter().map(|bound| self.expr(body, &bound.set)).collect();
        let bound: Vec<Param> = bounds
            .iter()
            .flat_map(|bound| pattern_slots(&bound.pattern))
            .map(|&slot| body.slot(slot))
            .collect();
        let operands = [self.operand(body, operand)];
        let data = self.apply_builtin(body, span, name, &operands, &ranges, &bound);
        (data, ranges.iter().map(|range| range.level).collect())
    }

    fn apply_items(&mut self, body: &Body, span: Span, name: &'static str, items: &[Expr]) -> Data {
        let operands = self.operands(body, items);
        self.apply_builtin(body, span, name, &operands, &[], &[])
    }

    fn apply_builtin(
        &mut self,
        body: &Body,
        span: Span,
        name: &'static str,
        operands: &[Operand],
        ranges: &[Data],
        bound: &[Param],
    ) -> Data {
        let operator = self.builtin(name);
        self.apply_operator(body, span, &operator, operands, ranges, bound)
    }

    fn apply_operator(
        &mut self,
        body: &Body,
        span: Span,
        operator: &Operator,
        operands: &[Operand],
        ranges: &[Data],
        bound: &[Param],
    ) -> Data {
        let (data, error) = apply(operator, operands, ranges, bound);
        if let Some(message) = error {
            self.error(body.def, span, message);
        }
        data
    }

    fn builtin_application(
        &mut self,
        body: &Body,
        expr: &Expr,
        op: Builtin,
        args: &[Expr],
    ) -> Data {
        let operands = self.operands(body, args);
        let name = builtin_name(op);
        let data = self.apply_builtin(body, expr.span, name, &operands, &[], &[]);
        let has_action = operands.iter().any(|operand| operand.data.level == Level::Action);
        match op {
            Builtin::Always | Builtin::Eventually => {
                if let (Some(arg), Some(operand)) = (args.first(), operands.first()) {
                    self.check_temporal(body, expr.span, op == Builtin::Always, arg, operand);
                }
            }
            Builtin::LeadsTo | Builtin::PlusArrow if has_action => {
                let message = "Action used where only temporal formula or state predicate allowed.";
                self.error(body.def, expr.span, message);
            }
            Builtin::And | Builtin::Or | Builtin::Implies | Builtin::Equiv => {
                self.check_junction(body, expr.span, name, &operands);
            }
            _ => {}
        }
        data
    }

    /// SANY allows an action under `[]` only as `[A]_v`, and under `<>` only as `<<A>>_v`. A
    /// `LET` hides the action from it.
    fn check_temporal(
        &mut self,
        body: &Body,
        span: Span,
        is_always: bool,
        arg: &Expr,
        operand: &Operand,
    ) {
        let is_subscripted = match arg.kind {
            ExprKind::BoxAction { .. } => is_always,
            ExprKind::AngleAction { .. } => !is_always,
            _ => false,
        };
        let is_raw_action =
            operand.data.level == Level::Action && body.is_application(arg.span) && !is_subscripted;
        if is_raw_action {
            let message = match is_always {
                true => "[] followed by action not of form [A]_v.",
                false => "<> followed by action not of form <<A>>_v.",
            };
            self.error(body.def, span, message);
        }
    }

    /// SANY rejects a logical operator applied to both a temporal formula and an action.
    fn check_junction(&mut self, body: &Body, span: Span, name: &str, operands: &[Operand]) {
        let has = |level| operands.iter().any(|operand| operand.data.level == level);
        if has(Level::Temporal) && has(Level::Action) {
            let message = format!("{name} has both temporal formula and action as arguments.");
            self.error(body.def, span, message);
        }
    }

    /// Whether a conjunction or disjunction is a bulleted list, which SANY names differently.
    fn is_bulleted(&self, body: &Body, span: Span) -> bool {
        let Some(def) = body.def else { return false };
        let source = &self.spec.modules[self.spec.def(def).module.index()].source;
        let text = source.get(span.start as usize..).unwrap_or_default();
        ["/\\", "\\/", "\u{2227}", "\u{2228}"].iter().any(|bullet| text.starts_with(bullet))
    }

    fn operands<E: std::borrow::Borrow<Expr>>(&mut self, body: &Body, exprs: &[E]) -> Vec<Operand> {
        exprs.iter().map(|expr| self.operand(body, expr.borrow())).collect()
    }

    /// An argument: an operator when it passes one, as tla-ts `toOperand`.
    pub(super) fn operand(&mut self, body: &Body, expr: &Expr) -> Operand {
        let ExprKind::OpArg(op) = &expr.kind else {
            return Operand::value(self.expr(body, expr));
        };
        match op {
            OpRef::Def { def, scope } => {
                // A partly applied operator of a parameterized instance, as in `F(I(x)!Op)`,
                // which SANY can't express: check the instance's arguments only.
                let mut scope = scope;
                while let Scope::Instance { parent, args } = scope {
                    self.operands(body, args);
                    scope = parent;
                }
                let operator = self.info(*def).own.clone();
                Operand { data: operator.data.clone(), operator: Some(operator), declared: None }
            }
            OpRef::Param(local) => self.declared(body.param(*local)),
            OpRef::Const(id) => self.declared(Param::Const(*id)),
            OpRef::Builtin(builtin) => {
                let operator = self.builtin(builtin_name(*builtin));
                Operand { data: operator.data.clone(), operator: Some(operator), declared: None }
            }
        }
    }

    fn declared(&self, param: Param) -> Operand {
        let mut data = Data::default();
        data.params.insert(param);
        Operand { data, operator: None, declared: Some((param, self.arity(param))) }
    }

    /// The operator a call applies, and the arguments of the parameterized instances around the
    /// definition. SANY applies `I(a)!Op(b)` as the operator `I!Op` of the parameters of `I` and
    /// `Op`.
    pub(super) fn callee<'e>(
        &mut self,
        def: DefId,
        scope: &'e Scope,
    ) -> (Rc<Operator>, Vec<&'e Expr>) {
        let mut groups = Vec::new();
        let mut frame = self.parent_frame(def);
        let mut scope = scope;
        while let Scope::Instance { parent, args } = scope {
            groups.push((frame, args));
            frame = frame.and_then(|frame| self.layout.frames[frame].parent);
            scope = parent;
        }
        let info = self.info(def);
        if groups.is_empty() {
            return (info.own.clone(), Vec::new());
        }
        groups.reverse();
        let args: Vec<&Expr> = groups.iter().flat_map(|(_, args)| args.iter()).collect();
        if let Some(view) = self.instance_view(def, groups.len()) {
            return (view, args);
        }
        let mut formals = Vec::new();
        let mut arities = Vec::new();
        for (frame, args) in &groups {
            let frame = frame.unwrap_or(usize::MAX);
            for slot in 0..args.len() {
                formals.push(Param::Slot(frame, slot));
                arities.push(self.arity(Param::Slot(frame, slot)));
            }
        }
        formals.extend(info.own.formals.iter().copied());
        arities.extend(self.spec.def(def).params.iter().copied());
        let view = Rc::new(self.view(def, &info.raw, &info.non_leibniz, formals, &arities));
        if self.is_done(def) {
            self.keep_instance_view(def, groups.len(), view.clone());
        }
        (view, args)
    }
}
