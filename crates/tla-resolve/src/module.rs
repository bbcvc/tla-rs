//! Loads modules and elaborates them: builds the names each module's units define, follows
//! `EXTENDS`, and instantiates modules for `INSTANCE`.

use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

use tla_ast::{Module, Name, Op, OpDecl, Span, Symbol, Unit};

use crate::expr::{FrameScope, apply, builtin_of};
use crate::ir::{
    Builtin, ConstId, Declaration, Def, DefBody, DefId, Expr, ExprKind, Local, ModuleId,
    ModuleInfo, OpRef, Scope, VarId,
};
use crate::levels::join;
use crate::levels::layout::{DefLayout, FrameLayout, Instantiation, Substituted, SubstitutedValue};
use crate::{ResolveError, Resolver, Result, stdlib};

/// What a name at module level stands for.
#[derive(Clone, Debug)]
pub(crate) enum Binding {
    Builtin(Builtin),
    Var(VarId),
    Const(ConstId),
    Def(DefId),
    /// A substitution simple enough to copy into each use, such as `x <- y`.
    Inline(Rc<Expr>),
    Instance(Rc<InstanceInfo>),
    /// A parameter or bound variable in a slot of the frame that binds it.
    Slot(usize),
}

/// The kinds SANY tells apart when the same name is defined twice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SymbolKind {
    Builtin,
    Variable,
    Constant,
    Operator,
    Module,
    /// An operator parameter or a bound variable.
    Parameter,
}

#[derive(Clone, Debug)]
pub(crate) struct Entry {
    pub binding: Binding,
    pub kind: SymbolKind,
    pub arity: usize,
    /// Where the symbol was declared or defined. Two entries from the same place are the same
    /// symbol reached two ways, which isn't a conflict.
    pub origin: Option<(ModuleId, Span)>,
    pub is_local: bool,
}

/// A named instance `I(params) == INSTANCE M ...`.
#[derive(Debug)]
pub(crate) struct InstanceInfo {
    pub params: Vec<usize>,
    /// The depth `I` is defined at. The definitions of the instance live one deeper when `I` has
    /// parameters, since a frame holds them.
    pub depth: usize,
    pub context: Rc<Context>,
}

/// The names visible at the top level of an elaborated module.
#[derive(Clone, Debug, Default)]
pub(crate) struct Context {
    pub names: HashMap<Symbol, Entry>,
}

impl Context {
    /// A context with the names of the operators TLA+ defines itself, which no module can
    /// redefine.
    fn with_builtins() -> Self {
        let named = [("BOOLEAN", Builtin::Boolean), ("STRING", Builtin::String)];
        let symbols = Op::ALL.iter().filter_map(|op| Some((op.name(), builtin_of(*op)?)));
        let names = named
            .into_iter()
            .chain(symbols)
            .map(|(name, builtin)| {
                let entry = Entry {
                    binding: Binding::Builtin(builtin),
                    kind: SymbolKind::Builtin,
                    arity: builtin.arity(),
                    origin: None,
                    is_local: false,
                };
                (Symbol::intern(name), entry)
            })
            .collect();
        Self { names }
    }
}

/// Checks `added` against a symbol already bound to the same name, following SANY's
/// `SymbolTable.addSymbol`. Returns whether `added` should replace nothing and be bound.
pub(crate) fn is_bindable(
    name: Symbol,
    current: Option<&Entry>,
    added: &Entry,
    is_bound_variable: bool,
) -> std::result::Result<bool, String> {
    let Some(current) = current else { return Ok(true) };
    if current.origin.is_some() && current.origin == added.origin {
        return Ok(false);
    }
    if current.kind == SymbolKind::Builtin {
        return Err(format!("Symbol {name} is a built-in operator, and cannot be redefined."));
    }
    if is_bound_variable || current.kind != added.kind || current.arity != added.arity {
        return Err(format!(
            "Multiply-defined symbol '{name}': this definition or declaration conflicts with an earlier one."
        ));
    }
    // SANY only warns about a second definition of the same kind and arity, and keeps the first.
    Ok(false)
}

/// The substitutions of one instantiation, by the name of each constant and variable.
pub(crate) struct Substitution {
    /// Tells instantiations apart, so the modules each one extends are elaborated once.
    pub id: usize,
    pub names: HashMap<Symbol, Binding>,
}

/// A constant or variable a module declares, itself or through `EXTENDS`.
#[derive(Clone, Debug)]
pub(crate) struct Parameter {
    pub name: Symbol,
    pub arity: usize,
    pub is_variable: bool,
}

pub(crate) struct ParsedModule {
    pub id: ModuleId,
    pub ast: Module,
}

/// The state of elaborating one module: its names so far and how deep its definitions are.
pub(crate) struct Elab {
    pub module: ModuleId,
    pub name: Symbol,
    pub context: Context,
    pub depth: usize,
    pub substitution: Option<Rc<Substitution>>,
}

impl Elab {
    pub fn add(&mut self, name: Name, entry: Entry, source: &str) -> Result<()> {
        let current = self.context.names.get(&name.symbol);
        match is_bindable(name.symbol, current, &entry, false) {
            Ok(true) => {
                self.context.names.insert(name.symbol, entry);
                Ok(())
            }
            Ok(false) => Ok(()),
            Err(message) => Err(ResolveError::new(self.name, source, name.span, message)),
        }
    }
}

impl Resolver<'_> {
    pub(crate) fn source(&self, module: ModuleId) -> Arc<str> {
        self.spec.modules[module.index()].source.clone()
    }

    pub(crate) fn error(
        &self,
        module: ModuleId,
        span: Span,
        message: impl Into<String>,
    ) -> ResolveError {
        ResolveError::new(
            self.spec.modules[module.index()].name,
            &self.source(module),
            span,
            message,
        )
    }

    pub(crate) fn add_module(
        &mut self,
        ast: Module,
        source: Arc<str>,
        is_standard: bool,
    ) -> Rc<ParsedModule> {
        let id = ModuleId(self.spec.modules.len() as u32);
        self.spec.modules.push(ModuleInfo { name: ast.name.symbol, source, is_standard });
        let parsed = Rc::new(ParsedModule { id, ast });
        self.parsed.insert(parsed.ast.name.symbol, parsed.clone());
        parsed
    }

    /// Finds a module by name: one parsed already, such as a module nested in another, then one
    /// from the loader, then a standard module.
    pub(crate) fn load(&mut self, name: Name, from: ModuleId) -> Result<Rc<ParsedModule>> {
        if let Some(parsed) = self.parsed.get(&name.symbol) {
            return Ok(parsed.clone());
        }
        let (source, is_standard) = match self.loader.load(name.symbol.as_str()) {
            Some(source) => (source, false),
            None => match stdlib::standard_module(name.symbol.as_str()) {
                Some(source) => (source.to_owned(), true),
                None => {
                    return Err(self.error(
                        from,
                        name.span,
                        format!("Cannot find source file for module {}.", name.symbol),
                    ));
                }
            },
        };
        let source: Arc<str> = source.into();
        let modules = tla_parser::parse_modules(&source).map_err(|error| ResolveError {
            message: error.message,
            module: name.symbol,
            span: error.span,
            line: error.line,
            column: error.column,
        })?;
        if modules[0].name.symbol != name.symbol {
            let message =
                format!("File for module {} holds module {}.", name.symbol, modules[0].name.symbol);
            return Err(self.error(from, name.span, message));
        }
        Ok(self.add_file(modules, source, is_standard))
    }

    /// Registers every top-level module of a file, and returns the first.
    pub(crate) fn add_file(
        &mut self,
        modules: Vec<Module>,
        source: Arc<str>,
        is_standard: bool,
    ) -> Rc<ParsedModule> {
        let mut added = modules
            .into_iter()
            .filter_map(|module| {
                let is_new = !self.parsed.contains_key(&module.name.symbol);
                is_new.then(|| self.add_module(module, source.clone(), is_standard))
            })
            .collect::<Vec<_>>();
        added.remove(0)
    }

    /// Registers the modules nested in `module` so that later units can extend or instantiate
    /// them.
    fn register_inner(&mut self, module: &Module, parent: ModuleId) -> Result<()> {
        for unit in &module.units {
            let Unit::Module(inner) = unit else { continue };
            let origin = (parent, inner.span);
            if self.parsed.contains_key(&inner.name.symbol) {
                if self.inner_origins.get(&inner.name.symbol) == Some(&origin) {
                    continue;
                }
                let message = format!(
                    "Multiply-defined module '{}': this definition or declaration conflicts with an earlier one.",
                    inner.name.symbol
                );
                return Err(self.error(parent, inner.name.span, message));
            }
            self.inner_origins.insert(inner.name.symbol, origin);
            let source = self.source(parent);
            let is_standard = self.spec.modules[parent.index()].is_standard;
            self.add_module(inner.clone(), source, is_standard);
        }
        Ok(())
    }

    /// The constants and variables a module declares, itself and through `EXTENDS`.
    pub(crate) fn parameters(&mut self, module: &Rc<ParsedModule>) -> Result<Vec<Parameter>> {
        if let Some(parameters) = self.parameters.get(&module.id) {
            return Ok(parameters.clone());
        }
        if self.in_progress.contains(&module.id) {
            return Err(self.error(
                module.id,
                module.ast.name.span,
                format!("Circular dependency involving module {}.", module.ast.name.symbol),
            ));
        }
        self.in_progress.push(module.id);
        let mut parameters: Vec<Parameter> = Vec::new();
        for extended in &module.ast.extends {
            let extended = self.load(*extended, module.id)?;
            for parameter in self.parameters(&extended)? {
                if !parameters.iter().any(|known| known.name == parameter.name) {
                    parameters.push(parameter);
                }
            }
        }
        for unit in &module.ast.units {
            let declared: Vec<Parameter> = match unit {
                Unit::Variables(names) => names
                    .iter()
                    .map(|name| Parameter { name: name.symbol, arity: 0, is_variable: true })
                    .collect(),
                Unit::Constants(decls) => decls
                    .iter()
                    .map(|decl| Parameter {
                        name: decl.name.symbol,
                        arity: decl.arity,
                        is_variable: false,
                    })
                    .collect(),
                _ => continue,
            };
            parameters.extend(declared);
        }
        self.in_progress.pop();
        self.parameters.insert(module.id, parameters.clone());
        Ok(parameters)
    }

    /// Elaborates a module without substitutions: the root module, the modules it extends, and
    /// modules without constants or variables. Each is elaborated once, at depth 0.
    pub(crate) fn plain(&mut self, module: &Rc<ParsedModule>) -> Result<Rc<Context>> {
        if let Some(context) = self.plain.get(&module.id) {
            return Ok(context.clone());
        }
        let frames = std::mem::take(&mut self.frames);
        let visible_from = std::mem::replace(&mut self.visible_from, 0);
        let is_instantiating = std::mem::replace(&mut self.is_instantiating, false);
        let context = self.elaborate(module, None, 0);
        self.frames = frames;
        self.visible_from = visible_from;
        self.is_instantiating = is_instantiating;
        let context = context?;
        self.plain.insert(module.id, context.clone());
        Ok(context)
    }

    /// Elaborates a module without constants or variables for use at the current depth: the
    /// shared plain elaboration, unless the module is nested in a module elaborated with
    /// substitutions, whose names it sees.
    fn shared(&mut self, module: &Rc<ParsedModule>) -> Result<Rc<Context>> {
        match self.enclosing.get(&module.id) {
            Some((_, false)) => self.elaborate(module, None, self.frames.len()),
            _ => self.plain(module),
        }
    }

    /// Elaborates `module` with the definitions at `depth`, which is the current number of
    /// frames. The module can't see the names of those frames.
    pub(crate) fn elaborate(
        &mut self,
        module: &Rc<ParsedModule>,
        substitution: Option<Rc<Substitution>>,
        depth: usize,
    ) -> Result<Rc<Context>> {
        if self.in_progress.contains(&module.id) {
            return Err(self.error(
                module.id,
                module.ast.name.span,
                format!("Circular dependency involving module {}.", module.ast.name.symbol),
            ));
        }
        self.in_progress.push(module.id);
        let visible_from = std::mem::replace(&mut self.visible_from, self.frames.len());
        let is_instantiating = self.is_instantiating;
        self.is_instantiating |= substitution.is_some();
        if self.is_instantiating {
            self.instantiated.insert(module.id);
        }
        let result = self.elaborate_units(module, substitution, depth);
        self.is_instantiating = is_instantiating;
        self.visible_from = visible_from;
        self.in_progress.pop();
        result.map(Rc::new)
    }

    fn elaborate_units(
        &mut self,
        module: &Rc<ParsedModule>,
        substitution: Option<Rc<Substitution>>,
        depth: usize,
    ) -> Result<Context> {
        let id = module.id;
        let source = self.source(id);
        self.register_inner(&module.ast, id)?;
        let mut elab = Elab {
            module: id,
            name: module.ast.name.symbol,
            // A nested module sees what its enclosing module defines before it, without
            // exporting it.
            context: self
                .enclosing
                .get(&id)
                .map_or_else(Context::with_builtins, |(context, _)| (**context).clone()),
            depth,
            substitution,
        };
        for extended in &module.ast.extends {
            let target = self.load(*extended, id)?;
            let context = match &elab.substitution {
                Some(substitution) if !self.parameters(&target)?.is_empty() => {
                    self.instance_context(&target, substitution.clone(), depth)?
                }
                _ => self.shared(&target)?,
            };
            for (name, entry) in &context.names {
                if !entry.is_local && entry.kind != SymbolKind::Builtin {
                    elab.add(Name { symbol: *name, span: extended.span }, entry.clone(), &source)?;
                }
            }
        }
        for unit in &module.ast.units {
            self.unit(&mut elab, unit, &source)?;
        }
        Ok(elab.context)
    }

    /// Elaborates an extended module under the substitutions of the instance that extends it,
    /// once per instance.
    fn instance_context(
        &mut self,
        module: &Rc<ParsedModule>,
        substitution: Rc<Substitution>,
        depth: usize,
    ) -> Result<Rc<Context>> {
        let key = (substitution.id, module.id);
        if let Some(context) = self.instances.get(&key) {
            return Ok(context.clone());
        }
        let context = self.elaborate(module, Some(substitution), depth)?;
        self.instances.insert(key, context.clone());
        Ok(context)
    }

    fn unit(&mut self, elab: &mut Elab, unit: &Unit, source: &str) -> Result<()> {
        match unit {
            Unit::Variables(names) => {
                for name in names {
                    let binding = match &elab.substitution {
                        Some(substitution) => substitution.names[&name.symbol].clone(),
                        None => {
                            self.spec.variables.push(Declaration {
                                name: name.symbol,
                                arity: 0,
                                module: elab.module,
                                span: name.span,
                            });
                            Binding::Var(VarId(self.spec.variables.len() as u32 - 1))
                        }
                    };
                    let entry = Entry {
                        binding,
                        kind: SymbolKind::Variable,
                        arity: 0,
                        origin: Some((elab.module, name.span)),
                        is_local: false,
                    };
                    elab.add(*name, entry, source)?;
                }
            }
            Unit::Constants(decls) => {
                for decl in decls {
                    let binding = match &elab.substitution {
                        Some(substitution) => substitution.names[&decl.name.symbol].clone(),
                        None => {
                            self.spec.constants.push(Declaration {
                                name: decl.name.symbol,
                                arity: decl.arity,
                                module: elab.module,
                                span: decl.name.span,
                            });
                            Binding::Const(ConstId(self.spec.constants.len() as u32 - 1))
                        }
                    };
                    let entry = Entry {
                        binding,
                        kind: SymbolKind::Constant,
                        arity: decl.arity,
                        origin: Some((elab.module, decl.name.span)),
                        is_local: false,
                    };
                    elab.add(decl.name, entry, source)?;
                }
            }
            Unit::Recursive(decls) => {
                for decl in decls {
                    let def = self.declare_recursive(elab.module, decl, elab.depth);
                    elab.add(
                        decl.name,
                        self.operator_entry(elab.module, decl.name, decl.arity, def, false),
                        source,
                    )?;
                }
            }
            Unit::Operator(definition) => {
                let def = self.operator(elab, definition)?;
                let entry = self.operator_entry(
                    elab.module,
                    definition.name,
                    definition.params.len(),
                    def,
                    definition.is_local,
                );
                elab.add(definition.name, entry, source)?;
            }
            Unit::Function(definition) => {
                let def = self.claim_def(elab, definition.name, Vec::new(), true)?;
                let entry =
                    self.operator_entry(elab.module, definition.name, 0, def, definition.is_local);
                elab.add(definition.name, entry, source)?;
                self.function(elab, def, definition)?;
            }
            Unit::Instance(instance) => {
                let context = self.instantiate(elab, instance, instance.span)?;
                for (name, entry) in &context.names {
                    let is_exported =
                        matches!(entry.kind, SymbolKind::Operator | SymbolKind::Module);
                    if !entry.is_local && is_exported {
                        let entry = Entry { is_local: instance.is_local, ..entry.clone() };
                        elab.add(
                            Name { symbol: *name, span: instance.module.span },
                            entry,
                            source,
                        )?;
                    }
                }
            }
            Unit::ModuleDef(definition) => {
                let info = self.named_instance(elab, definition)?;
                let entry = Entry {
                    binding: Binding::Instance(info),
                    kind: SymbolKind::Module,
                    arity: definition.params.len(),
                    origin: Some((elab.module, definition.name.span)),
                    is_local: definition.is_local,
                };
                elab.add(definition.name, entry, source)?;
            }
            Unit::Assume(assume) => {
                let def = self.statement(elab, assume.name, &assume.expr)?;
                if !assume.is_axiom {
                    self.spec.assumptions.push(def);
                }
                if let Some(name) = assume.name {
                    elab.add(name, self.operator_entry(elab.module, name, 0, def, false), source)?;
                }
            }
            Unit::Theorem(theorem) => {
                if let (Some(name), Some(statement)) = (theorem.name, &theorem.statement) {
                    let def = self.statement(elab, Some(name), statement)?;
                    elab.add(name, self.operator_entry(elab.module, name, 0, def, false), source)?;
                }
            }
            Unit::Module(inner) => {
                let id = self.parsed[&inner.name.symbol].id;
                let mut context = elab.context.clone();
                context.names.values_mut().for_each(|entry| entry.is_local = true);
                let is_plain = elab.substitution.is_none() && elab.depth == 0;
                if !is_plain {
                    self.plain.remove(&id);
                }
                self.enclosing.insert(id, (Rc::new(context), is_plain));
            }
        }
        Ok(())
    }

    /// Resolves the expression of an `ASSUME` or a theorem as a zero-arity definition.
    fn statement(
        &mut self,
        elab: &Elab,
        name: Option<Name>,
        expr: &tla_ast::Expr,
    ) -> Result<DefId> {
        let name = name.unwrap_or(Name { symbol: Symbol::intern("ASSUME"), span: expr.span });
        let def = self.new_def(elab.module, name, Vec::new(), elab.depth);
        self.push_frame(Vec::new());
        let body = self.expr(elab, expr);
        let frame = self.frames.pop().unwrap();
        self.finish_def(def, DefBody::Expr(body?), frame);
        Ok(def)
    }

    pub(crate) fn operator_entry(
        &self,
        module: ModuleId,
        name: Name,
        arity: usize,
        def: DefId,
        is_local: bool,
    ) -> Entry {
        Entry {
            binding: Binding::Def(def),
            kind: SymbolKind::Operator,
            arity,
            origin: Some((module, name.span)),
            is_local,
        }
    }

    pub(crate) fn new_def(
        &mut self,
        module: ModuleId,
        name: Name,
        params: Vec<usize>,
        depth: usize,
    ) -> DefId {
        self.spec.defs.push(Def {
            name: name.symbol,
            module,
            span: name.span,
            params,
            body: DefBody::Expr(Expr::new(ExprKind::Bool(false), name.span)),
            frame_size: 0,
            depth,
        });
        self.layout.defs.push(DefLayout {
            qualifier: self.qualifier.clone(),
            is_instantiated: self.is_instantiating,
            ..DefLayout::default()
        });
        let id = DefId(self.spec.defs.len() as u32 - 1);
        self.pending.insert(id);
        id
    }

    /// Gives `def` its body, and the frame that holds its parameters and bound variables.
    pub(crate) fn finish_def(&mut self, def: DefId, body: DefBody, frame: FrameScope) {
        let def_mut = &mut self.spec.defs[def.index()];
        def_mut.body = body;
        def_mut.frame_size = frame.slots;
        self.layout.frames[frame.id].params = def_mut.params.clone();
        let layout = &mut self.layout.defs[def.index()];
        layout.frame = Some(frame.id);
        layout.lets = frame.lets;
        layout.let_bodies = frame.let_bodies;
        self.pending.remove(&def);
    }

    /// Starts a frame inside the current one. `params` are the arities of the parameters of a
    /// parameterized instance whose frame it is.
    pub(crate) fn push_frame(&mut self, params: Vec<usize>) {
        let id = self.layout.frames.len();
        let parent = self.frames.last().map(|frame| frame.id);
        self.layout.frames.push(FrameLayout { parent, params });
        self.frames.push(FrameScope { id, ..FrameScope::default() });
    }

    pub(crate) fn declare_recursive(
        &mut self,
        module: ModuleId,
        decl: &OpDecl,
        depth: usize,
    ) -> DefId {
        let section = self.pending_section(module).unwrap_or_else(|| {
            self.sections += 1;
            self.sections
        });
        let def = self.new_def(module, decl.name, vec![0; decl.arity], depth);
        self.recursive.insert((module, decl.name.symbol, depth), def);
        let layout = &mut self.layout.defs[def.index()];
        layout.is_recursive = true;
        layout.section = Some(section);
        def
    }

    /// The `RECURSIVE` section of `module` whose operators aren't all defined yet. SANY checks
    /// the definitions made until they are with them.
    pub(crate) fn pending_section(&self, module: ModuleId) -> Option<usize> {
        let mut pending = self.recursive.iter().filter(|((pending, ..), _)| *pending == module);
        pending.next().and_then(|(_, def)| self.layout.defs[def.index()].section)
    }

    /// Instantiates the module an `INSTANCE` names, with its definitions at the current depth.
    /// `span` is the whole `INSTANCE`, or `I == INSTANCE ...`.
    pub(crate) fn instantiate(
        &mut self,
        elab: &Elab,
        instance: &tla_ast::Instance,
        span: Span,
    ) -> Result<Rc<Context>> {
        let target = self.load(instance.module, elab.module)?;
        let parameters = self.parameters(&target)?;
        let depth = self.frames.len();
        let mut substitution = HashMap::new();
        for explicit in &instance.substitutions {
            let Some(parameter) =
                parameters.iter().find(|parameter| parameter.name == explicit.name.symbol)
            else {
                return Err(self.error(
                    elab.module,
                    explicit.name.span,
                    format!(
                        "{} is not a CONSTANT or VARIABLE of module {}.",
                        explicit.name.symbol, instance.module.symbol
                    ),
                ));
            };
            let binding =
                self.substitute(elab, explicit.name, parameter.arity, &explicit.value, depth)?;
            substitution.insert(explicit.name.symbol, binding);
        }
        for parameter in &parameters {
            if substitution.contains_key(&parameter.name) {
                continue;
            }
            let name = Name { symbol: parameter.name, span: instance.module.span };
            let implicit = tla_ast::Expr::new(
                tla_ast::ExprKind::Apply { name, args: Vec::new() },
                instance.module.span,
            );
            let binding =
                self.substitute(elab, name, parameter.arity, &implicit, depth).map_err(|_| {
                    self.error(
                        elab.module,
                        instance.module.span,
                        format!(
                            "The INSTANCE of module {} has no substitution for {}.",
                            instance.module.symbol, parameter.name
                        ),
                    )
                })?;
            substitution.insert(parameter.name, binding);
        }
        if parameters.is_empty() {
            return self.shared(&target);
        }
        let substitutions = parameters
            .iter()
            .map(|parameter| Substituted {
                name: parameter.name,
                is_variable: parameter.is_variable,
                arity: parameter.arity,
                value: match &substitution[&parameter.name] {
                    Binding::Inline(expr) => SubstitutedValue::Inline((**expr).clone()),
                    Binding::Def(def) => SubstitutedValue::Def(*def),
                    _ => unreachable!("a substitution is a definition or an inlined value"),
                },
            })
            .collect();
        self.layout.instantiations.push(Instantiation {
            module: target.id,
            instancer: elab.module,
            span,
            substitutions,
            is_instantiated: self.is_instantiating,
            order: self.spec.defs.len(),
        });
        self.substitutions += 1;
        let substitution = Substitution { id: self.substitutions, names: substitution };
        self.elaborate(&target, Some(Rc::new(substitution)), depth)
    }

    /// Resolves the value of `name <- value` as a definition at `depth`, or as an expression to
    /// copy into each use when it is simple enough.
    fn substitute(
        &mut self,
        elab: &Elab,
        name: Name,
        arity: usize,
        value: &tla_ast::Expr,
        depth: usize,
    ) -> Result<Binding> {
        self.push_frame(Vec::new());
        let resolved = if arity == 0 {
            self.expr(elab, value)
        } else {
            for _ in 0..arity {
                self.alloc_slot();
            }
            self.op_arg(elab, value, arity).map(|op| {
                let args = (0..arity)
                    .map(|slot| Expr::new(ExprKind::Local(Local { hops: 0, slot }), value.span))
                    .collect();
                match op {
                    // Applying another definition to the same parameters is that definition.
                    OpRef::Def { def, scope: Scope::Global | Scope::Up(_) } => Expr::new(
                        ExprKind::OpArg(OpRef::Def { def, scope: Scope::Global }),
                        value.span,
                    ),
                    op => Expr::new(apply(op, args), value.span),
                }
            })
        };
        let frame = self.frames.pop().unwrap();
        let resolved = resolved?;
        match &resolved.kind {
            ExprKind::OpArg(OpRef::Def { def, .. }) => return Ok(Binding::Def(*def)),
            ExprKind::Call { def, scope: Scope::Global | Scope::Up(_), args }
                if args.is_empty() =>
            {
                return Ok(Binding::Def(*def));
            }
            _ if is_inlinable(&resolved) => return Ok(Binding::Inline(Rc::new(resolved))),
            _ => {}
        }
        let def = self.new_def(elab.module, name, vec![0; arity], depth);
        self.layout.defs[def.index()].is_substitution = true;
        self.finish_def(def, DefBody::Expr(resolved), frame);
        Ok(Binding::Def(def))
    }

    pub(crate) fn named_instance(
        &mut self,
        elab: &Elab,
        definition: &tla_ast::ModuleDef,
    ) -> Result<Rc<InstanceInfo>> {
        let depth = self.frames.len();
        let has_params = !definition.params.is_empty();
        if has_params {
            self.push_frame(definition.params.iter().map(|param| param.arity).collect());
            for param in &definition.params {
                self.bind_slot(elab, param.name, param.arity)?;
            }
        }
        let outer = self.qualifier.clone();
        let qualifier = format!("{}{}!", outer.as_deref().unwrap_or(""), definition.name.symbol);
        self.qualifier = Some(qualifier.into());
        let span = join(definition.name.span, definition.instance.span);
        let context = self.instantiate(elab, &definition.instance, span);
        self.qualifier = outer;
        if has_params {
            self.frames.pop();
        }
        Ok(Rc::new(InstanceInfo {
            params: definition.params.iter().map(|param| param.arity).collect(),
            depth,
            context: context?,
        }))
    }
}

/// Whether a resolved substitution can be copied into every use: it reads no frame, so it means
/// the same at any depth, and it is small.
fn is_inlinable(expr: &Expr) -> bool {
    matches!(
        expr.kind,
        ExprKind::Bool(_)
            | ExprKind::Int(_)
            | ExprKind::Str(_)
            | ExprKind::Var(_)
            | ExprKind::Const(_)
    )
}
