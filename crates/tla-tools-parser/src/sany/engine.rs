//! The code JavaCC generates for a grammar, run over SANY's: the parse-mode code of each
//! production, the `jj_3` routines that scan a lookahead, and the `ParseException` the parser
//! throws.

use std::rc::Rc;

use super::grammar::{Predicate, Repeat, Unit, UnitKind, production};
use super::kinds::{Kinds, kind};
use super::lexer::escape;
use super::{Frame, LookaheadCall, Node, State};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Scan {
    Matched,
    Failed,
    Done,
}

fn evaluate_semantic(state: &mut State, semantic: &Predicate) -> bool {
    state.is_looking_ahead = true;
    let is_passed = semantic(state);
    state.is_looking_ahead = false;
    is_passed
}

/// `jj_scan_token`, which also records how far past the current token `jj_rescan_token`
/// scans, the length of the longest token sequence the ParseException expects.
fn scan_token(state: &mut State, kinds: &Kinds) -> Scan {
    if state.scan_position == state.last_position {
        state.remaining -= 1;
        state.last_position = state.next(state.scan_position);
    }
    state.scan_position = state.next(state.scan_position);
    if state.is_rescanning {
        let mut position = 0;
        let mut token = Some(state.token);
        while let Some(index) = token
            && index != state.scan_position
            && position < 100
        {
            position += 1;
            token = state.tokens[index].next;
        }
        if token.is_some() && position < 100 {
            state.farthest_rescan = state.farthest_rescan.max(position);
        }
    }
    if !kinds.contains(state.kind_of(state.scan_position)) {
        return Scan::Failed;
    }
    match state.remaining == 0 && state.scan_position == state.last_position {
        true => Scan::Done,
        false => Scan::Matched,
    }
}

/// The `jj_3` routines, which match an expansion without running its actions. A loop or
/// option skips its body's lookahead, but a choice checks the semantic part of each
/// alternative's.
fn scan(state: &mut State, unit: &'static Unit) -> Scan {
    match &unit.kind {
        UnitKind::Tokens(kinds) => scan_token(state, kinds),
        UnitKind::Call(name) => scan(state, &production(name).body),
        UnitKind::Action(_) => Scan::Matched,
        UnitKind::Lookahead { semantic, .. } => match semantic {
            Some(semantic) if !evaluate_semantic(state, semantic) => Scan::Failed,
            _ => Scan::Matched,
        },
        UnitKind::Sequence(units) => {
            for (index, inner) in units.iter().enumerate() {
                if index == 0 && matches!(inner.kind, UnitKind::Lookahead { .. }) {
                    continue;
                }
                let result = scan(state, inner);
                if result != Scan::Matched {
                    return result;
                }
            }
            Scan::Matched
        }
        UnitKind::Choice(alternatives) => {
            let start = state.scan_position;
            for alternative in alternatives {
                let is_passed = match alternative.head_lookahead().map(|head| &head.kind) {
                    Some(UnitKind::Lookahead { semantic: Some(semantic), .. }) => {
                        evaluate_semantic(state, semantic)
                    }
                    _ => true,
                };
                let result = if is_passed { scan(state, alternative) } else { Scan::Failed };
                if result != Scan::Failed {
                    return result;
                }
                state.scan_position = start;
            }
            Scan::Failed
        }
        UnitKind::Repeat(repeat, body) => {
            let start = state.scan_position;
            let first = scan(state, body);
            if first == Scan::Failed {
                state.scan_position = start;
                return match repeat {
                    Repeat::OneOrMore => Scan::Failed,
                    _ => Scan::Matched,
                };
            }
            if first == Scan::Done || *repeat == Repeat::Optional {
                return first;
            }
            loop {
                let iteration_start = state.scan_position;
                match scan(state, body) {
                    Scan::Done => return Scan::Done,
                    Scan::Failed => {
                        state.scan_position = iteration_start;
                        return Scan::Matched;
                    }
                    Scan::Matched => {}
                }
            }
        }
    }
}

/// A `jj_2` call, which scans `expansion` with a budget of `amount` new tokens. It saves the
/// call for `jj_rescan_token` as `jj_save` does, over a call of the same site that can't be
/// rescanned.
fn scan_ahead(state: &mut State, amount: i64, expansion: &'static Unit) -> bool {
    state.remaining = amount;
    state.scan_position = state.token;
    state.last_position = state.token;
    let is_matched = scan(state, expansion) != Scan::Failed;
    let call = LookaheadCall {
        generation: state.generation + amount - state.remaining,
        first: state.token,
        amount,
    };
    let generation = state.generation;
    let site = state.calls.iter().position(|(site, _)| std::ptr::eq(*site, expansion));
    let chain = match site {
        Some(site) => &mut state.calls[site].1,
        None => {
            state.calls.push((expansion, Vec::new()));
            &mut state.calls.last_mut().expect("just pushed").1
        }
    };
    match chain.iter().position(|saved| saved.generation <= generation) {
        Some(stale) => chain[stale] = call,
        None => chain.push(call),
    }
    is_matched
}

/// The index of the alternative that the generated code's lookahead checks choose. As
/// `ParseEngine.buildLookaheadChecker` builds them, a check is the semantic lookahead alone
/// where no tokens are needed, a `jj_ntk` switch where one token decides, and a `jj_2` call
/// otherwise.
fn decide(state: &mut State, alternatives: &'static [Unit]) -> Option<usize> {
    alternatives.iter().position(|alternative| {
        let (amount, expansion, semantic) =
            match alternative.head_lookahead().map(|head| &head.kind) {
                Some(UnitKind::Lookahead { amount, expansion, semantic }) => {
                    (*amount, expansion.as_deref().unwrap_or(alternative), semantic.as_ref())
                }
                _ => (1, alternative, None),
            };
        let analysis = expansion.analysis();
        let passes = |state: &mut State| semantic.is_none_or(|semantic| semantic(state));
        if amount == 0 || analysis.is_nullable {
            return passes(state);
        }
        if amount == 1 && semantic.is_none() && !analysis.has_semantic_start {
            let next = state.get_token(1);
            if analysis.first.contains(state.kind_of(next)) {
                return true;
            }
            state.failed_switch_generation = state.generation;
            return false;
        }
        scan_ahead(state, amount, expansion) && passes(state)
    })
}

/// `ParseExceptionExtended.getShortMessage` for the ParseException that
/// `generateParseException` builds, which shows as many tokens as the longest token sequence
/// it expects. A rescan that finishes its lookahead ends the rescans of its site.
fn encountered(state: &mut State) -> String {
    state.is_rescanning = true;
    let calls = state.calls.clone();
    for (expansion, chain) in calls {
        let generation = state.generation;
        for call in chain.iter().filter(|saved| saved.generation > generation) {
            state.remaining = call.amount;
            state.scan_position = call.first;
            state.last_position = call.first;
            if scan(state, expansion) == Scan::Done {
                break;
            }
        }
    }
    state.is_rescanning = false;
    let switched = usize::from(state.failed_switch_generation == state.generation);
    let length = switched.max(state.farthest_rescan);
    let mut images = Vec::new();
    let next = state.next(state.token);
    let mut token = next;
    for index in 0..length {
        if state.kind_of(token) == kind("EOF") {
            images.push("<EOF>".to_owned());
            break;
        }
        images.push(state.token(token).image.clone());
        // SANY's message follows the tokens the parser has read, without reading another.
        if index + 1 < length {
            token = state.next(token);
        }
    }
    let next = state.token(next);
    format!(
        "Encountered \"{}\" at line {}, column {} and token \"{}\" ",
        images.join(" "),
        next.line,
        next.column,
        escape(&state.token(state.token).image)
    )
}

/// Records `TLAplusParser.msgStackToString`'s report, without its `***Parse Error***`
/// heading, and returns false.
fn fail(state: &mut State, message: Option<String>) -> bool {
    let expecting = match state.expecting {
        "" => String::new(),
        expecting => format!("Was expecting \"{expecting}\"\n"),
    };
    let message = message.unwrap_or_else(|| encountered(state));
    let mut stack = String::new();
    for (name, token) in state.messages.iter().rev().take(5) {
        let token = state.token(*token);
        stack.push_str(&format!(
            "{name} starting at line {}, column {}.\n",
            token.line, token.column
        ));
    }
    state.report = Some(format!("{expecting}{message}\n\nResidual stack trace follows:\n{stack}"));
    false
}

fn consume(state: &mut State, kinds: &Kinds) -> bool {
    let next = state.next(state.token);
    if !kinds.contains(state.kind_of(next)) {
        state.failed_switch_generation = state.generation;
        return fail(state, None);
    }
    state.token = next;
    state.generation += 1;
    let node = Rc::new(Node { kind: "token", heirs: Vec::new(), first: next, last: next });
    state.frames.last_mut().expect("a production is being parsed").heirs.push(node);
    true
}

/// Parses a production, and adds the node it returns to those of the production that called
/// it.
pub(super) fn parse_production(state: &mut State, name: &'static str) -> bool {
    let production = production(name);
    if let Some(message) = production.message {
        let token = state.get_token(1);
        state.messages.push((message, token));
        state.expecting = "";
    }
    state.frames.push(Frame::default());
    if !parse(state, &production.body) {
        return false;
    }
    let mut frame = state.frames.pop().expect("the production's frame");
    if production.message.is_some() {
        state.messages.pop();
        state.expecting = "";
    }
    if let Some(exit) = &production.exit
        && let Some(message) = exit(&mut frame, state)
    {
        return fail(state, Some(message));
    }
    let node = match frame.node {
        Some(node) => Some(node),
        None if frame.heirs.is_empty() => None,
        None => Some(Node::new(name, frame.heirs)),
    };
    if let (Some(node), Some(caller)) = (node, state.frames.last_mut()) {
        caller.heirs.push(node);
    }
    true
}

/// Runs the parse-mode code JavaCC generates for `unit`. It returns false once a
/// ParseException's report is recorded.
fn parse(state: &mut State, unit: &'static Unit) -> bool {
    match &unit.kind {
        UnitKind::Tokens(kinds) => consume(state, kinds),
        UnitKind::Call(name) => parse_production(state, name),
        UnitKind::Action(run) => match run(state) {
            Some(message) => fail(state, Some(message)),
            None => true,
        },
        UnitKind::Lookahead { semantic, .. } => match semantic {
            Some(semantic) if !semantic(state) => fail(state, None),
            _ => true,
        },
        UnitKind::Sequence(units) => units.iter().enumerate().all(|(index, inner)| {
            (index == 0 && matches!(inner.kind, UnitKind::Lookahead { .. })) || parse(state, inner)
        }),
        UnitKind::Choice(alternatives) => match decide(state, alternatives) {
            Some(index) => parse(state, &alternatives[index]),
            None => fail(state, None),
        },
        UnitKind::Repeat(repeat, body) => {
            let body: &'static Unit = body;
            if *repeat == Repeat::OneOrMore && !parse(state, body) {
                return false;
            }
            if *repeat == Repeat::Optional {
                return decide(state, std::slice::from_ref(body)).is_none() || parse(state, body);
            }
            while decide(state, std::slice::from_ref(body)) == Some(0) {
                if !parse(state, body) {
                    return false;
                }
            }
            true
        }
    }
}
