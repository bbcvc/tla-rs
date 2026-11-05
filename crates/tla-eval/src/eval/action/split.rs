//! TLC's split of a next-state relation into the actions it names in a behavior, in
//! `TLCGet("action")`, and in coverage: `Tool.getActions`, ported from tla-ts's `getActions` in
//! `spec-description.ts`.
//!
//! The split follows the relation through disjunctions, through `\E` over sets it can compute
//! as constants, one action for each witness, and into the definitions it calls with constant
//! arguments. Anything else is an action, named after the definition it is in, with the values
//! of that definition's parameters.

use std::sync::Arc;

use tla_ast::{Quantifier, Span};
use tla_resolve::{Builtin, DefBody, DefId, Expr, ExprKind, Scope};
use tla_value::{Symbol, Value};

use super::run::{Computation, Run};
use super::{Action, Rest, Site};
use crate::env::{Enabled, Env, Frame, Slot, SpecRef};
use crate::eval::analysis::is_constant;
use crate::{Evaluator, Result, State};

/// One of the actions TLC splits a next-state relation into.
///
/// TLC keeps a call of a definition of a module instantiated with substitutions whole, names it
/// as SANY does, `I!Op`, and places it at the `INSTANCE`, or at the call when it can't compute
/// the arguments as constants.
#[derive(Clone)]
pub struct NextAction {
    /// The definition TLC names the action after, as SANY names it: the one whose body holds
    /// it, or that a call TLC keeps whole applies.
    pub name: Symbol,
    /// The parameters of that definition and their values, which TLC prints after the name.
    pub parameters: Vec<(Symbol, Value)>,
    /// Where the action is: its expression, or the call TLC doesn't split further.
    pub module: tla_resolve::ModuleId,
    pub span: Span,
    /// The relation split.
    pub(crate) next: DefId,
    pub(crate) body: Body,
}

#[derive(Clone)]
pub(crate) enum Body {
    /// The relation's definition, which TLC evaluates rather than walks.
    Definition,
    Expr {
        expr: SpecRef<Expr>,
        site: Site,
    },
}

impl NextAction {
    /// TLC's `Action.getInvocationSignature`: the name and the values of the parameters, as in
    /// `Send(1,2)`.
    pub fn signature(&self) -> String {
        if self.parameters.is_empty() {
            return self.name.to_string();
        }
        let values: Vec<String> =
            self.parameters.iter().map(|(_, value)| value.to_string()).collect();
        format!("{}({})", self.name, values.join(","))
    }
}

/// The definition whose body the split is in, and the name TLC gives it.
struct Closure {
    name: Symbol,
    def: DefId,
}

impl Evaluator {
    /// TLC's split of the zero-arity action definition `next` into the actions it names, in
    /// TLC's order. TLC computes it once, when it starts, so the evaluator keeps it.
    pub(crate) fn split_next(&self, next: DefId) -> Result<Arc<[NextAction]>> {
        if let Some(actions) = self.lock_actions().get(&next) {
            return Ok(actions.clone());
        }
        let actions: Arc<[NextAction]> = self.split_definition(next)?.into();
        Ok(self.lock_actions().entry(next).or_insert(actions).clone())
    }

    fn lock_actions(
        &self,
    ) -> std::sync::MutexGuard<'_, std::collections::HashMap<DefId, Arc<[NextAction]>>> {
        self.next_actions.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    fn split_definition(&self, next: DefId) -> Result<Vec<NextAction>> {
        if let Some(error) = self.zero_arity_problem(next) {
            return Err(error);
        }
        // TLC splits the definition the configuration replaces `next` with.
        let Some(target) = self.walked(next, 0) else {
            let info = self.spec.def(next);
            let action = NextAction {
                name: info.name,
                parameters: Vec::new(),
                module: info.module,
                span: info.span,
                next,
                body: Body::Definition,
            };
            return Ok(vec![action]);
        };
        let info = self.spec.def(target);
        let site = Site {
            frame: Arc::new(Frame::new(Vec::new(), info.frame_size, None)),
            module: info.module,
            enabled: Enabled::Outside,
        };
        let DefBody::Expr(body) = &info.body else { unreachable!("a walked definition") };
        let mut actions = Vec::new();
        let closure = Closure { name: info.name, def: target };
        self.split(body, &site, &closure, next, &mut actions);
        Ok(actions)
    }

    fn split(
        &self,
        expr: &Expr,
        site: &Site,
        closure: &Closure,
        next: DefId,
        actions: &mut Vec<NextAction>,
    ) {
        match &expr.kind {
            ExprKind::Or(items) | ExprKind::Builtin { op: Builtin::Or, args: items } => {
                for item in items {
                    self.split(item, site, closure, next, actions);
                }
            }
            ExprKind::Quant { quantifier: Quantifier::Exists, bounds, body } => {
                let start = actions.len();
                let result =
                    self.variables(bounds, &mut constant_env(site)).and_then(|variables| {
                        self.for_each_bound_site(&variables, site, |bound| {
                            self.split(body, bound, closure, next, actions);
                            Ok(true)
                        })
                    });
                // TLC takes an `\E` it can't enumerate as a constant, or one without witnesses,
                // for a single action.
                if result.is_err() || actions.len() == start {
                    actions.truncate(start);
                    actions.push(self.split_action(expr, site, closure, next));
                }
            }
            ExprKind::Call { def, scope, args } => {
                self.split_call(*def, scope, args, expr, site, closure, next, actions);
            }
            _ => actions.push(self.split_action(expr, site, closure, next)),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn split_call(
        &self,
        def: DefId,
        scope: &Scope,
        args: &[Expr],
        expr: &Expr,
        site: &Site,
        closure: &Closure,
        next: DefId,
        actions: &mut Vec<NextAction>,
    ) {
        // TLC splits the definition the configuration replaces `def` with.
        let Some(target) = self.walked(def, args.len()) else {
            actions.push(self.split_action(expr, site, closure, next));
            return;
        };
        let info = self.spec.def(target);
        // As SANY names the operator a reference applies: I!Op through the instance I.
        let name = self.spec.qualified_names.get(&(site.module, expr.span)).copied();
        let name = name.unwrap_or(info.name);
        let call = |parameters: Vec<(Symbol, Value)>, (module, span)| NextAction {
            name,
            parameters,
            module,
            span,
            next,
            body: Body::Expr { expr: self.spec_ref(expr), site: site.clone() },
        };
        let at_call = (site.module, expr.span);
        let are_constant = args.iter().all(|arg| is_constant(&self.spec, arg));
        // TLC keeps an action of a module instantiated with substitutions whole, at the INSTANCE
        // with the values of constant arguments, and at the call otherwise.
        if info.is_instantiated {
            let instance = self.spec.instance_spans.get(&target).copied().unwrap_or(at_call);
            let action = match are_constant.then(|| self.constant_values(args, site)).flatten() {
                Some(values) => call(self.named(target, values), instance),
                None if args.is_empty() => call(Vec::new(), instance),
                None => call(Vec::new(), at_call),
            };
            actions.push(action);
            return;
        }
        if !are_constant || self.is_constant_value(target) {
            actions.push(call(Vec::new(), at_call));
            return;
        }
        let Some(values) = self.constant_values(args, site) else {
            actions.push(call(Vec::new(), at_call));
            return;
        };
        let parent =
            if target == def { self.scope_frame(scope, &constant_env(site)) } else { Ok(None) };
        let Ok(parent) = parent else {
            actions.push(call(Vec::new(), at_call));
            return;
        };
        let DefBody::Expr(body) = &info.body else { unreachable!("a walked definition") };
        let slots = values.into_iter().map(Slot::Value).collect();
        let callee = Site {
            frame: Arc::new(Frame::new(slots, info.frame_size, parent)),
            module: info.module,
            enabled: site.enabled,
        };
        let closure = Closure { name, def: target };
        self.split(body, &callee, &closure, next, actions);
    }

    /// The values of `args`, if TLC computes them as constants.
    fn constant_values(&self, args: &[Expr], site: &Site) -> Option<Vec<Value>> {
        let mut env = constant_env(site);
        args.iter().map(|arg| self.eval(arg, &mut env).ok()).collect()
    }

    /// Whether `def` is a definition TLC computes as a constant when it starts, which it
    /// doesn't split: tla-ts's `isConstantValue`.
    fn is_constant_value(&self, def: DefId) -> bool {
        matches!(&self.spec.def(def).body, DefBody::Expr(body)
            if !matches!(body.kind, ExprKind::Int(_) | ExprKind::Str(_)))
            && self.is_computed_once(def)
            && self.constant_value(def).is_ok()
    }

    /// The parameters of `def`, named, with `values`.
    fn named(&self, def: DefId, values: Vec<Value>) -> Vec<(Symbol, Value)> {
        let names = self.spec.param_names.get(&def).map(Vec::as_slice).unwrap_or_default();
        let unnamed = Symbol::intern("_");
        let names = names.iter().copied().chain(std::iter::repeat(unnamed));
        names.zip(values).collect()
    }

    /// The action `expr` of `site` in `closure`, named after the closure.
    fn split_action(&self, expr: &Expr, site: &Site, closure: &Closure, next: DefId) -> NextAction {
        let params = self.spec.def(closure.def).params.len();
        let values = site.frame.slots[..params]
            .iter()
            .filter_map(|slot| match slot {
                Slot::Value(value) => Some(value.clone()),
                _ => None,
            })
            .collect();
        let parameters = self.named(closure.def, values);
        NextAction {
            name: closure.name,
            parameters,
            module: site.module,
            span: expr.span,
            next,
            body: Body::Expr { expr: self.spec_ref(expr), site: site.clone() },
        }
    }

    fn spec_ref(&self, expr: &Expr) -> SpecRef<Expr> {
        // SAFETY: the split walks expressions of this evaluator's spec.
        unsafe { SpecRef::new(&self.spec, expr) }
    }

    /// The successors of `state` under `action` alone, in TLC's order, repeats included.
    pub(crate) fn enumerate_action(
        &self,
        action: &NextAction,
        state: &State,
        found: &mut dyn FnMut(State) -> Result<bool>,
    ) -> Result<()> {
        let Body::Expr { expr, site } = &action.body else {
            return self.enumerate_next(action.next, state, found);
        };
        let mut run = Run::new(self, Computation::Next, Some(state), action.next, Some(found));
        let named = Action::default().called(action.name);
        self.act(expr.get(), site, &mut run, named, &Rest::Done)
    }

    /// TLC's `Action.getLocation`: the signature and the range of the action.
    pub(crate) fn label_action(&self, action: &NextAction) -> String {
        let source = &self.spec.modules[action.module.index()].source;
        let span = without_trailing_layout(source, action.span);
        format!("{} {}", action.signature(), self.range_of(action.module, span))
    }
}

/// `span` up to its last token: the parser ends a bulleted list where the next line starts,
/// after the whitespace and comments that follow it, and SANY ends it at its last token.
fn without_trailing_layout(source: &str, span: Span) -> Span {
    let Some(text) = source.get(span.start as usize..span.end as usize) else { return span };
    let bytes = text.as_bytes();
    let (mut index, mut end, mut depth) = (0, 0, 0usize);
    while index < bytes.len() {
        match (bytes[index], bytes.get(index + 1)) {
            (b'(', Some(b'*')) => {
                depth += 1;
                index += 2;
            }
            (b'*', Some(b')')) if depth > 0 => {
                depth -= 1;
                index += 2;
            }
            _ if depth > 0 => index += 1,
            (b'\\', Some(b'*')) => {
                index = text[index..].find('\n').map_or(bytes.len(), |line| index + line);
            }
            (b'"', _) => {
                index += 1;
                while index < bytes.len() && bytes[index] != b'"' {
                    index += if bytes[index] == b'\\' { 2 } else { 1 };
                }
                index += 1;
                end = index.min(bytes.len());
            }
            (byte, _) if byte.is_ascii_whitespace() => index += 1,
            _ => {
                index += 1;
                end = index;
            }
        }
    }
    match end {
        0 => span,
        end => Span::new(span.start as usize, span.start as usize + end),
    }
}

/// The context TLC splits the relation in: without states, so that an expression that reads a
/// variable fails.
fn constant_env(site: &Site) -> Env<'static> {
    Env {
        frame: site.frame.clone(),
        module: site.module,
        state: None,
        next: None,
        keep_lazy: false,
        enabled: Enabled::Outside,
    }
}

#[cfg(test)]
mod layout_tests {
    use super::*;

    #[test]
    fn ends_a_span_at_its_last_token() {
        let source = "/\\ x' = 1 \\* done\n  (* more *)\n\n";
        let span = Span::new(0, source.len());
        assert_eq!(without_trailing_layout(source, span), Span::new(0, 9));
        let source = "x' = \"a \\\" (*\"  ";
        let span = Span::new(0, source.len());
        assert_eq!(without_trailing_layout(source, span).end as usize, source.len() - 2);
    }
}
