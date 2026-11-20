//! SANY's linter (`tla2sany.linter.Linter`), ported from tla-ts `sany/linter.ts`: it warns about a
//! record field named like a definition or declaration of the module, as `[foo |-> 1]` where the
//! module defines `foo`, since the field doesn't take the definition's value.
//!
//! SANY spares a record whose fields, or those of another record with the same field names, are
//! built from declarations: such a record is taken to model the declared things by name.

use std::collections::{HashMap, HashSet};

use tla_tools_ast::{Name, Span, Symbol};

use crate::ir::{Builtin, DefBody, DefId, ExceptKey, Expr, ExprKind, ModuleId, Spec};
use crate::module::{Binding, SymbolKind};
use crate::{Message, Resolver};

/// A record constructor or a set of records, as resolution made it in a module elaborated by
/// itself.
pub(crate) struct Record {
    pub module: ModuleId,
    pub fields: Vec<(Name, Expr)>,
}

impl Resolver<'_> {
    /// Keeps a record for the linter, unless it is resolved under the substitutions of an
    /// `INSTANCE`, which SANY doesn't lint, or again.
    pub(crate) fn keep_record(
        &mut self,
        module: ModuleId,
        span: Span,
        fields: &[(Name, tla_tools_ast::Expr)],
        values: &[(Symbol, Expr)],
    ) {
        let is_own = !self.is_instantiating && self.replaying == 0 && self.speculative == 0;
        if is_own && self.record_spans.insert((module, span)) {
            let names = fields.iter().map(|(name, _)| *name);
            let fields = names.zip(values.iter().map(|(_, value)| value.clone())).collect();
            self.records.push(Record { module, fields });
        }
    }

    /// The linter's warnings for every module elaborated by itself, each module's in the order
    /// of its records.
    pub(crate) fn lint(&self) -> Vec<Message> {
        let mut by_module: HashMap<ModuleId, Vec<&Record>> = HashMap::new();
        for record in &self.records {
            by_module.entry(record.module).or_default().push(record);
        }
        let mut warnings = Vec::new();
        let mut checker = Checker { spec: &self.spec, visited: HashSet::new() };
        for record in &self.records {
            let Some(context) = self.plain.get(&record.module) else { continue };
            // The records of the module and of the modules it extends, directly or not.
            let modules = self.extended_by(record.module);
            let exempt = modules
                .iter()
                .flat_map(|module| by_module.get(module).into_iter().flatten())
                .filter(|other| is_same_domain(other, record))
                .flat_map(|other| &other.fields)
                .any(|(_, value)| checker.is_built_from_declarations(value));
            if exempt {
                continue;
            }
            for (name, _) in &record.fields {
                let Some(entry) = context.names.get(&name.symbol) else { continue };
                if entry.kind == SymbolKind::Builtin || matches!(entry.binding, Binding::Slot(_)) {
                    continue;
                }
                let (module, span) = entry.location;
                let field = name.symbol;
                let message = format!(
                    "The field name \"{field}\" in the record constructor is identical to the existing definition or declaration\nnamed {field}, located at {}.\nThe field in the record will not take the value of the {field} definition or declaration.\nIn TLA+, field names in records are strings, regardless of any similarly named declarations or definitions.\nTherefore, DOMAIN [{field} |-> ...] = {{\"{field}\"}} holds true.",
                    self.location(module, span)
                );
                let error = self.error(record.module, name.span, message);
                let analyzed = self.file_module(record.module);
                warnings.push(Message { error, analyzed, is_warning: true });
            }
        }
        warnings
    }

    /// `module` and the modules it extends, directly or not (`ModuleNode.getExtendedModuleSet`).
    fn extended_by(&self, module: ModuleId) -> HashSet<ModuleId> {
        let mut found = HashSet::from([module]);
        let mut pending = vec![module];
        while let Some(module) = pending.pop() {
            let name = self.spec.modules[module.index()].name;
            let Some(parsed) = self.parsed.get(&name) else { continue };
            for extended in &parsed.ast.extends {
                if let Some(extended) = self.parsed.get(&extended.symbol)
                    && found.insert(extended.id)
                {
                    pending.push(extended.id);
                }
            }
        }
        found
    }
}

/// `Records.sameDomain`: whether two records have the same field names.
fn is_same_domain(record: &Record, other: &Record) -> bool {
    if record.fields.len() != other.fields.len() {
        return false;
    }
    let names: HashSet<Symbol> = other.fields.iter().map(|(name, _)| name.symbol).collect();
    record.fields.iter().all(|(name, _)| names.contains(&name.symbol))
}

struct Checker<'a> {
    spec: &'a Spec,
    visited: HashSet<DefId>,
}

impl Checker<'_> {
    /// `Linter.isBuiltFromDeclarations`: whether an expression applies a declared or bound name,
    /// `BOOLEAN`, or `Nat` or `Int` of their standard modules, directly or through the
    /// definitions it applies. SANY compares a definition's name with its module's, so no
    /// definition of `Real` counts.
    fn is_built_from_declarations(&mut self, expr: &Expr) -> bool {
        let found = match &expr.kind {
            ExprKind::Var(_)
            | ExprKind::Const(_)
            | ExprKind::Local(_)
            | ExprKind::CallParam { .. }
            | ExprKind::CallConst { .. } => true,
            ExprKind::Builtin { op: Builtin::Boolean, .. } => true,
            ExprKind::Call { def, .. } => self.is_def_built_from_declarations(*def),
            _ => false,
        };
        found || children(expr).into_iter().any(|child| self.is_built_from_declarations(child))
    }

    fn is_def_built_from_declarations(&mut self, def: DefId) -> bool {
        let definition = self.spec.def(def);
        let module = self.spec.modules[definition.module.index()].name;
        let set = match module.as_str() {
            "Naturals" => "Nat",
            "Integers" => "Int",
            _ => "",
        };
        if definition.name.as_str() == set {
            return true;
        }
        if !self.visited.insert(def) {
            return false;
        }
        match &definition.body {
            DefBody::Expr(body) => self.is_built_from_declarations(body),
            DefBody::Function { bounds, body } => {
                bounds.iter().any(|bound| self.is_built_from_declarations(&bound.set))
                    || self.is_built_from_declarations(body)
            }
        }
    }
}

/// The subexpressions of an expression.
fn children(expr: &Expr) -> Vec<&Expr> {
    match &expr.kind {
        ExprKind::Call { args, .. }
        | ExprKind::CallParam { args, .. }
        | ExprKind::CallConst { args, .. }
        | ExprKind::Builtin { args, .. }
        | ExprKind::And(args)
        | ExprKind::Or(args)
        | ExprKind::SetEnum(args)
        | ExprKind::Tuple(args)
        | ExprKind::Product(args) => args.iter().collect(),
        ExprKind::If { cond, then, otherwise } => vec![&**cond, &**then, &**otherwise],
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
        ExprKind::UnboundedQuant { body, .. } => vec![&**body],
        ExprKind::Choose { set, body, .. } => set.as_deref().into_iter().chain([&**body]).collect(),
        ExprKind::SetFilter { bound, pred } => vec![&bound.set, &**pred],
        ExprKind::Record(fields) | ExprKind::RecordSet(fields) => {
            fields.iter().map(|(_, value)| value).collect()
        }
        ExprKind::FuncSet { domain, range } => vec![&**domain, &**range],
        ExprKind::FuncApp { func, args } => [&**func].into_iter().chain(args).collect(),
        ExprKind::Dot { record, .. } => vec![&**record],
        ExprKind::Except { base, updates } => {
            let mut children = vec![&**base];
            for update in updates {
                for key in &update.path {
                    if let ExceptKey::Apply(args) = key {
                        children.extend(args);
                    }
                }
                children.push(&update.value);
            }
            children
        }
        ExprKind::BoxAction { action, sub } | ExprKind::AngleAction { action, sub } => {
            vec![&**action, &**sub]
        }
        ExprKind::Fairness { sub, action, .. } => vec![&**sub, &**action],
        ExprKind::Bool(_)
        | ExprKind::Int(_)
        | ExprKind::Str(_)
        | ExprKind::Var(_)
        | ExprKind::Const(_)
        | ExprKind::Local(_)
        | ExprKind::OpArg(_) => Vec::new(),
    }
}
