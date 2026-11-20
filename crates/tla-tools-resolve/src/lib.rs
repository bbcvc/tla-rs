//! Resolves the names in a TLA+ specification.
//!
//! [`resolve`] parses a root module, loads every module it extends or instantiates, and turns
//! the whole specification into a [`Spec`] whose expressions refer to state variables,
//! constants, local slots, and definitions instead of names. It follows SANY's scoping rules:
//! a definition is visible after it, `RECURSIVE` declares an operator ahead of its definition,
//! `LOCAL` definitions aren't exported, and a name can't be defined twice with a different
//! meaning.
//!
//! [`analyze`] goes on after an error, as SANY does, and returns every error and warning SANY
//! reports, with the warnings of SANY's linter for a spec it accepts.
//!
//! TLC's standard modules are bundled. A loader supplies the other modules, and a module it
//! supplies takes precedence over a standard module of the same name.

mod expr;
mod ir;
mod levels;
mod lint;
mod module;
mod order;
mod recover;
mod selection;
mod stdlib;

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub use ir::*;
pub use order::{SanyModuleOrder, sany_module_order, tlc_string_order, tlc_variable_order};
use tla_tools_ast::{Span, Symbol};

use crate::expr::FrameScope;
use crate::levels::layout::Layout;
use crate::module::{Binding, Context, Parameter, ParsedModule};

/// Supplies the source of a module by name, or `None` if it has no such module.
pub trait ModuleLoader {
    fn load(&mut self, name: &str) -> Option<String>;
}

impl<F: FnMut(&str) -> Option<String>> ModuleLoader for F {
    fn load(&mut self, name: &str) -> Option<String> {
        self(name)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("line {line}, column {column} of module {module}: {message}")]
pub struct ResolveError {
    pub message: String,
    pub module: Symbol,
    pub span: Span,
    pub line: usize,
    pub column: usize,
    /// The line and column of the last character of what the error is about, which SANY's
    /// range of it ends at.
    pub end_line: usize,
    pub end_column: usize,
    pub kind: ErrorKind,
}

/// Which part of SANY reports an error.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorKind {
    /// The parser rejects the text of a module.
    Syntax,
    /// The semantic analysis or the level checking of a module rejects it.
    Semantic,
    /// SANY can't read a module it needs.
    Fatal,
}

impl ResolveError {
    pub(crate) fn new(
        module: Symbol,
        source: &str,
        span: Span,
        message: impl Into<String>,
    ) -> Self {
        let (line, column) = span.line_column(source);
        // What the error is about ends at its last token, not at the white space after it.
        let text = source.get(span.start as usize..span.end as usize).unwrap_or_default();
        let end = span.start as usize + text.trim_end().len();
        let last = end.saturating_sub(1).max(span.start as usize);
        let (end_line, end_column) = Span::new(last, last + 1).line_column(source);
        let kind = ErrorKind::Semantic;
        Self { message: message.into(), module, span, line, column, end_line, end_column, kind }
    }

    /// A syntax error the parser reports in `module`.
    fn syntax(module: Symbol, error: tla_tools_parser::ParseError) -> Self {
        Self {
            message: error.message,
            module,
            span: error.span,
            line: error.line,
            column: error.column,
            end_line: error.line,
            end_column: error.column,
            kind: ErrorKind::Syntax,
        }
    }
}

pub(crate) type Result<T> = std::result::Result<T, ResolveError>;

/// A message SANY prints about a spec, an error or a warning, with the module it was analyzing
/// when it found it, after which it prints it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Message {
    pub error: ResolveError,
    /// The module SANY was analyzing, which may not be the one the message is located in.
    pub analyzed: Symbol,
    pub is_warning: bool,
}

/// What SANY makes of a spec: every error and warning it reports, and the spec when there is no
/// error.
#[derive(Debug)]
pub struct Analysis {
    pub spec: Option<Spec>,
    /// The messages in the order resolution found them. [`Analysis::in_sany_order`] puts them in
    /// SANY's.
    pub messages: Vec<Message>,
    /// Whether the errors are level errors, which SANY reports for one module only.
    pub is_level_checked: bool,
    /// The warnings of SANY's linter, which lints a spec it accepts.
    pub lints: Vec<Message>,
}

impl Analysis {
    pub fn errors(&self) -> impl Iterator<Item = &ResolveError> {
        self.messages.iter().filter(|message| !message.is_warning).map(|message| &message.error)
    }

    pub fn warnings(&self) -> impl Iterator<Item = &ResolveError> {
        self.messages.iter().filter(|message| message.is_warning).map(|message| &message.error)
    }

    /// Puts the messages in the order SANY reports them, given the order it analyzes the
    /// modules in: a module's messages after those of the modules analyzed before it. SANY
    /// level-checks a module only while it has found no error, so it reports the level errors of
    /// the first module that has any.
    pub fn in_sany_order(&mut self, analyzed: &[String]) {
        let rank = |message: &Message| {
            analyzed.iter().position(|name| name == message.analyzed.as_str()).unwrap_or(usize::MAX)
        };
        self.messages.sort_by_key(rank);
        if self.is_level_checked {
            let errors = self.messages.iter().filter(|message| !message.is_warning);
            if let Some(first) = errors.map(rank).min() {
                self.messages.retain(|message| message.is_warning || rank(message) == first);
            }
        }
    }
}

/// Parses `source` as the root module and resolves it with the modules it uses, stopping at the
/// first error.
pub fn resolve(source: &str, loader: &mut dyn ModuleLoader) -> Result<Spec> {
    let analysis = analyze(source, loader);
    match analysis.spec {
        Some(spec) => Ok(spec),
        None => Err(analysis.errors().next().cloned().expect("a spec without errors resolves")),
    }
}

/// Parses `source` as the root module and resolves it with the modules it uses, going on after
/// an error where SANY does, to report every error and warning SANY reports.
pub fn analyze(source: &str, loader: &mut dyn ModuleLoader) -> Analysis {
    let fail = |error: ResolveError| Analysis {
        spec: None,
        messages: vec![Message { analyzed: error.module, error, is_warning: false }],
        is_level_checked: false,
        lints: Vec::new(),
    };
    let modules = match tla_tools_parser::parse_modules(source) {
        Ok(modules) => modules,
        Err(error) => return fail(ResolveError::syntax(Symbol::intern(""), error)),
    };
    let mut resolver = Resolver {
        loader,
        spec: Spec {
            modules: Vec::new(),
            variables: Vec::new(),
            constants: Vec::new(),
            defs: Vec::new(),
            assumptions: Vec::new(),
            root: HashMap::new(),
            levels: Vec::new(),
            instance_variables: HashMap::new(),
            param_names: HashMap::new(),
            qualified_names: HashMap::new(),
            instance_spans: HashMap::new(),
            statements: HashSet::new(),
        },
        parsed: HashMap::new(),
        parameters: HashMap::new(),
        plain: HashMap::new(),
        instances: HashMap::new(),
        substitutions: 0,
        in_progress: Vec::new(),
        frames: Vec::new(),
        visible_from: 0,
        at_slots: Vec::new(),
        pending: HashSet::new(),
        recursive: HashMap::new(),
        enclosing: HashMap::new(),
        inner_origins: HashMap::new(),
        layout: Layout::default(),
        qualifier: None,
        instance_span: None,
        is_instantiating: false,
        instantiated: HashSet::new(),
        sections: 0,
        elabs: 0,
        elab_contexts: HashMap::new(),
        origins: HashMap::new(),
        statements: HashSet::new(),
        replaying: 0,
        messages: Vec::new(),
        speculative: 0,
        is_level_checked: false,
        is_circular: false,
        records: Vec::new(),
        record_spans: HashSet::new(),
    };
    let resolved = resolver.run(modules, source);
    let mut messages = std::mem::take(&mut resolver.messages);
    match resolved {
        Ok(()) => {}
        // SANY reads every module before it analyzes any, so an error reading one is its only.
        Err(error) if !resolver.is_recoverable(&error) => return fail(error),
        Err(error) => messages.push(Message { analyzed: error.module, error, is_warning: false }),
    }
    let is_accepted = messages.iter().all(|message| message.is_warning);
    let lints = if is_accepted { resolver.lint() } else { Vec::new() };
    let spec = is_accepted.then_some(resolver.spec);
    Analysis { spec, messages, is_level_checked: resolver.is_level_checked, lints }
}

impl Resolver<'_> {
    fn run(&mut self, modules: Vec<tla_tools_ast::Module>, source: &str) -> Result<()> {
        let root = self.add_file(modules, source.into(), false);
        let context = self.plain(&root)?;
        let extended = self.extends_closure(&root);
        let defs = &self.spec.defs;
        self.spec.assumptions.retain(|def| extended.contains(&defs[def.index()].module));
        let mut pending: Vec<DefId> = self.pending.iter().copied().collect();
        pending.sort();
        for def in pending {
            let def = self.spec.def(def);
            let (module, span) = (def.module, def.span);
            let message =
                format!("Symbol {} declared in RECURSIVE statement but not defined.", def.name);
            let error = self.error(module, self.declaration_extent(module, span), message);
            self.report(module, error, false);
        }
        if self.messages.iter().any(|message| !message.is_warning) {
            return Ok(());
        }
        self.spec.root = context
            .names
            .iter()
            .filter_map(|(name, entry)| {
                let root = match entry.binding {
                    Binding::Var(id) => RootName::Var(id),
                    Binding::Const(id) => RootName::Const(id),
                    Binding::Def(id) => RootName::Def(id),
                    _ => return None,
                };
                Some((*name, root))
            })
            .collect();
        self.check_levels();
        self.spec.statements = std::mem::take(&mut self.statements);
        Ok(())
    }

    /// `root` and the modules it extends, directly or not.
    fn extends_closure(&self, root: &ParsedModule) -> HashSet<ModuleId> {
        let mut closure = HashSet::from([root.id]);
        let mut pending = vec![root];
        while let Some(module) = pending.pop() {
            for name in &module.ast.extends {
                if let Some(extended) = self.parsed.get(&name.symbol)
                    && closure.insert(extended.id)
                {
                    pending.push(extended);
                }
            }
        }
        closure
    }
}

pub(crate) struct Resolver<'l> {
    loader: &'l mut dyn ModuleLoader,
    spec: Spec,
    parsed: HashMap<Symbol, Rc<ParsedModule>>,
    parameters: HashMap<ModuleId, Vec<Parameter>>,
    plain: HashMap<ModuleId, Rc<Context>>,
    /// Modules extended by an instantiated module, by instantiation.
    instances: HashMap<(usize, ModuleId), Rc<Context>>,
    substitutions: usize,
    /// Modules being elaborated, to report circular dependencies.
    in_progress: Vec<ModuleId>,
    frames: Vec<FrameScope>,
    /// The first frame whose names the current code can see. A module instantiated inside a
    /// frame can't see the names of the frames around the `INSTANCE`.
    visible_from: usize,
    /// The frame depth and slot of the old value `@` stands for in each enclosing `EXCEPT`.
    at_slots: Vec<(usize, usize)>,
    /// Definitions created but not yet resolved.
    pending: HashSet<DefId>,
    /// `RECURSIVE` declarations awaiting their definitions, by module, name, and depth.
    recursive: HashMap<(ModuleId, Symbol, usize), DefId>,
    /// What each nested module sees of the module around it.
    /// Whether that module was elaborated plainly, so the nested module can be too.
    enclosing: HashMap<ModuleId, (Rc<Context>, bool)>,
    /// The enclosing module and place of each nested module, to tell a second elaboration of
    /// it from a different module of the same name.
    inner_origins: HashMap<Symbol, (ModuleId, Span)>,
    /// What the level pass needs to know of the program beyond the IR.
    layout: Layout,
    /// `I!J!` while elaborating the module of the named instance `J` in that of `I`.
    qualifier: Option<Rc<str>>,
    /// The outermost `INSTANCE` with substitutions being elaborated, which the definitions it
    /// makes record.
    instance_span: Option<(ModuleId, Span)>,
    /// Whether a module is being elaborated under the substitutions of an `INSTANCE`.
    is_instantiating: bool,
    /// The modules elaborated under the substitutions of an `INSTANCE`.
    instantiated: HashSet<ModuleId>,
    /// The number of `RECURSIVE` sections so far.
    sections: usize,
    /// The number of elaborations started so far.
    elabs: usize,
    /// The names each finished elaboration defined, by [`module::Elab::id`].
    elab_contexts: HashMap<usize, Rc<Context>>,
    /// Where each module-level definition comes from, for subexpression references to it.
    origins: HashMap<DefId, selection::Origin>,
    /// Whether a subexpression reference is resolving part of a definition again, whose names
    /// may hide later ones without conflict.
    replaying: usize,
    /// The definitions of theorems and assumptions, named or not. A `HIDE` may cite a named one.
    statements: HashSet<DefId>,
    /// The errors and warnings found so far.
    messages: Vec<Message>,
    /// Whether resolution is trying something whose errors aren't SANY's, which therefore stop
    /// it rather than being reported.
    speculative: usize,
    /// Whether the level checking ran, which it does only when there is no other error.
    is_level_checked: bool,
    /// Whether a module was found to depend on itself, which stops resolution.
    is_circular: bool,
    /// The records the linter checks, and where they are, to keep each once.
    records: Vec<lint::Record>,
    record_spans: HashSet<(ModuleId, Span)>,
}

/// Whether TLC bundles a module of this name. A loader shouldn't supply one from a library
/// directory, since TLC finds its own first.
pub fn is_standard_module(name: &str) -> bool {
    stdlib::standard_module(name).is_some()
}
