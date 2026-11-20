//! Going on after an error, as SANY does, to report every error of a spec rather than the first.
//!
//! SANY's semantic analysis records an error and goes on: an expression it can't resolve becomes
//! a placeholder, and a definition it rejects is left out. Resolution does the same at two
//! places: an expression ([`Resolver::expr`]) and a unit of a module. Each takes a checkpoint
//! of the resolver's state before, and puts it back after an error, since an error can leave a
//! frame or a binding half made.
//!
//! It also has the places SANY locates what it reports at, which aren't always where the error
//! is found.

use std::collections::HashSet;
use std::rc::Rc;

use tla_tools_ast::{Span, Symbol};

use crate::ir::{DefId, ModuleId};
use crate::module::ParsedModule;
use crate::{ErrorKind, Message, ResolveError, Resolver, Result};

/// The state an error may leave half changed.
pub(crate) struct Checkpoint {
    frames: usize,
    /// The names of the innermost frame.
    names: usize,
    at_slots: usize,
    visible_from: usize,
    qualifier: Option<Rc<str>>,
    instance_span: Option<(ModuleId, Span)>,
    is_instantiating: bool,
    replaying: usize,
    in_progress: usize,
    defs: usize,
    /// The `RECURSIVE` declarations awaiting their definitions, for a checkpoint of a unit.
    awaiting: Vec<DefId>,
}

impl Resolver<'_> {
    /// The state to go back to after an error in an expression.
    pub(crate) fn checkpoint(&self) -> Checkpoint {
        Checkpoint {
            frames: self.frames.len(),
            names: self.frames.last().map_or(0, |frame| frame.names.len()),
            at_slots: self.at_slots.len(),
            visible_from: self.visible_from,
            qualifier: self.qualifier.clone(),
            instance_span: self.instance_span,
            is_instantiating: self.is_instantiating,
            replaying: self.replaying,
            in_progress: self.in_progress.len(),
            defs: self.spec.defs.len(),
            awaiting: Vec::new(),
        }
    }

    /// The state to go back to after an error in a unit, which may have claimed the definition a
    /// `RECURSIVE` declaration awaits.
    pub(crate) fn unit_checkpoint(&self) -> Checkpoint {
        Checkpoint { awaiting: self.recursive.values().copied().collect(), ..self.checkpoint() }
    }

    /// Reports an error SANY goes on after, found while analyzing `analyzed`, and returns
    /// `fallback` in place of what failed. Any other error stops resolution.
    pub(crate) fn recover<T>(
        &mut self,
        at: Checkpoint,
        analyzed: ModuleId,
        result: Result<T>,
        fallback: impl FnOnce() -> T,
    ) -> Result<T> {
        match result {
            Err(error) if self.speculative == 0 && self.is_recoverable(&error) => {
                self.restore(at);
                self.report(analyzed, error, false);
                Ok(fallback())
            }
            result => result,
        }
    }

    fn restore(&mut self, at: Checkpoint) {
        self.frames.truncate(at.frames);
        if let Some(frame) = self.frames.last_mut() {
            frame.names.truncate(at.names);
        }
        self.at_slots.truncate(at.at_slots);
        self.visible_from = at.visible_from;
        self.qualifier = at.qualifier;
        self.instance_span = at.instance_span;
        self.is_instantiating = at.is_instantiating;
        self.replaying = at.replaying;
        self.in_progress.truncate(at.in_progress);
        // A definition left unfinished isn't one awaiting its `RECURSIVE` declaration's.
        let awaiting: HashSet<DefId> = self.recursive.values().copied().collect();
        let claimed: HashSet<DefId> = at.awaiting.into_iter().collect();
        self.pending.retain(|def| {
            awaiting.contains(def) || (def.index() < at.defs && !claimed.contains(def))
        });
    }

    /// Records an error or a warning found while analyzing `analyzed`. SANY keeps a message once.
    pub(crate) fn report(&mut self, analyzed: ModuleId, error: ResolveError, is_warning: bool) {
        if self.speculative > 0 {
            return;
        }
        let message = Message { error, analyzed: self.file_module(analyzed), is_warning };
        if !self.messages.contains(&message) {
            self.messages.push(message);
        }
    }

    /// The module whose file `module` is in: SANY locates what is in an inner module in the
    /// module of its file.
    pub(crate) fn file_module(&self, module: ModuleId) -> Symbol {
        let mut name = self.spec.modules[module.index()].name;
        while let Some(&(parent, _)) = self.inner_origins.get(&name) {
            name = self.spec.modules[parent.index()].name;
        }
        name
    }

    /// Whether SANY goes on after an error: it stops at an error of syntax, a module it can't
    /// read, and a circular dependency among modules, after which nothing is resolved.
    pub(crate) fn is_recoverable(&self, error: &ResolveError) -> bool {
        error.kind == ErrorKind::Semantic && !self.is_circular
    }

    /// The error of a module that depends on itself, which resolution stops at.
    pub(crate) fn circular(&mut self, module: &ParsedModule) -> ResolveError {
        self.is_circular = true;
        let message = format!("Circular dependency involving module {}.", module.ast.name.symbol);
        self.error(module.id, module.ast.name.span, message)
    }

    /// SANY's description of a place, as in `line 2, col 1 to line 2, col 7 of module M`.
    pub(crate) fn location(&self, module: ModuleId, span: Span) -> String {
        let at = self.error(module, span, "");
        format!(
            "line {}, col {} to line {}, col {} of module {}",
            at.line, at.column, at.end_line, at.end_column, at.module
        )
    }

    /// The operator token in `gap`, without the white space, comments and parentheses around it.
    pub(crate) fn token_in(&self, module: ModuleId, gap: Span) -> Span {
        let source = self.source(module);
        let (mut start, mut end) = (gap.start as usize, gap.end as usize);
        let text = |start: usize, end: usize| source.get(start..end).unwrap_or_default();
        loop {
            let rest = text(start, end);
            let trimmed = rest.trim_start().trim_start_matches(')');
            let trimmed = skip_comment_start(trimmed);
            if trimmed.len() == rest.len() {
                break;
            }
            start += rest.len() - trimmed.len();
        }
        loop {
            let rest = text(start, end);
            let trimmed = rest.trim_end().trim_end_matches('(');
            let trimmed = skip_comment_end(trimmed);
            if trimmed.len() == rest.len() {
                break;
            }
            end = start + trimmed.len();
        }
        Span::new(start, end.max(start))
    }

    /// Where SANY locates a `RECURSIVE` declaration of `name`: the name and its parameters, as
    /// in `F(_, _)`.
    pub(crate) fn declaration_extent(&self, module: ModuleId, name: Span) -> Span {
        let source = self.source(module);
        let rest = &source[name.end as usize..];
        let after = rest.trim_start();
        if !after.starts_with('(') {
            return name;
        }
        let open = name.end as usize + (rest.len() - after.len());
        match after.find(')') {
            Some(close) => Span::new(name.start as usize, open + close + 1),
            None => name,
        }
    }
}

/// `text` after a comment it starts with.
fn skip_comment_start(text: &str) -> &str {
    if let Some(rest) = text.strip_prefix("(*") {
        return rest.find("*)").map_or(text, |end| &rest[end + 2..]);
    }
    if text.starts_with("\\*") {
        return text.find('\n').map_or("", |end| &text[end..]);
    }
    text
}

/// `text` before a comment it ends with.
fn skip_comment_end(text: &str) -> &str {
    if let Some(rest) = text.strip_suffix("*)") {
        return rest.rfind("(*").map_or(text, |start| &rest[..start]);
    }
    text
}
