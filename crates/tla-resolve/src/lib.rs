//! Resolves the names in a TLA+ specification.
//!
//! [`resolve`] parses a root module, loads every module it extends or instantiates, and turns
//! the whole specification into a [`Spec`] whose expressions refer to state variables,
//! constants, local slots, and definitions instead of names. It follows SANY's scoping rules:
//! a definition is visible after it, `RECURSIVE` declares an operator ahead of its definition,
//! `LOCAL` definitions aren't exported, and a name can't be defined twice with a different
//! meaning.
//!
//! TLC's standard modules are bundled. A loader supplies the other modules, and a module it
//! supplies takes precedence over a standard module of the same name.

mod expr;
mod ir;
mod levels;
mod module;
mod stdlib;

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub use ir::*;
use tla_ast::{Span, Symbol};

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
}

impl ResolveError {
    pub(crate) fn new(
        module: Symbol,
        source: &str,
        span: Span,
        message: impl Into<String>,
    ) -> Self {
        let (line, column) = span.line_column(source);
        Self { message: message.into(), module, span, line, column }
    }
}

pub(crate) type Result<T> = std::result::Result<T, ResolveError>;

/// Parses `source` as the root module and resolves it with the modules it uses.
pub fn resolve(source: &str, loader: &mut dyn ModuleLoader) -> Result<Spec> {
    let modules = tla_parser::parse_modules(source).map_err(|error| ResolveError {
        message: error.message,
        module: Symbol::intern(""),
        span: error.span,
        line: error.line,
        column: error.column,
    })?;
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
        is_instantiating: false,
        sections: 0,
    };
    let root = resolver.add_file(modules, source.into(), false);
    let context = resolver.plain(&root)?;
    if let Some(&def) = resolver.pending.iter().min() {
        let def = resolver.spec.def(def);
        let message =
            format!("The operator {} was declared RECURSIVE but never defined.", def.name);
        return Err(resolver.error(def.module, def.span, message));
    }
    resolver.spec.root = context
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
    resolver.check_levels()?;
    Ok(resolver.spec)
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
    /// Whether a module is being elaborated under the substitutions of an `INSTANCE`.
    is_instantiating: bool,
    /// The number of `RECURSIVE` sections so far.
    sections: usize,
}

/// Whether TLC bundles a module of this name. A loader shouldn't supply one from a library
/// directory, since TLC finds its own first.
pub fn is_standard_module(name: &str) -> bool {
    stdlib::standard_module(name).is_some()
}
