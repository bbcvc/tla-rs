//! The Java code of `TLAplusParser` that the grammar's semantic lookaheads and actions call.

use std::sync::LazyLock;

use super::grammar::{Unit, action};
use super::kinds::{self, Kind, Kinds, kind};
use super::lexer::Token;
use super::{Node, State};

/// `TLAplusParser.isOp`, `isInfixOp`, `isPostfixOp`, and `isFieldNameToken`.
pub(super) static OPERATOR_KINDS: LazyLock<Kinds> =
    LazyLock::new(|| Kinds::of(kinds::range("op_57", "op_119")));
pub(super) static INFIX_KINDS: LazyLock<Kinds> =
    LazyLock::new(|| Kinds::of(kinds::range("op_1", "op_119")));
pub(super) static POSTFIX_KINDS: LazyLock<Kinds> =
    LazyLock::new(|| Kinds::of(kinds::range("op_57", "op_70")));
pub(super) static FIELD_NAME_KINDS: LazyLock<Kinds> = LazyLock::new(|| {
    Kinds::of(
        kinds::range("ACTION", "EXCEPT")
            .chain([kind("EXTENDS")])
            .chain(kinds::range("IF", "SF"))
            .chain([kind("STATE")])
            .chain(kinds::range("THEN", "WITH"))
            .chain([kind("US")])
            .chain(kinds::range("op_112", "op_116")),
    )
});

/// `JunctionListContext.isAboveCurrent`: whether `column` is right of the current junction
/// list's bullet.
pub(super) fn is_above(state: &State, column: u32) -> bool {
    state.junctions.last().is_none_or(|junction| junction.column < column)
}

/// `isAboveCurrent` for the next token.
pub(super) fn is_above_current(state: &mut State) -> bool {
    let token = state.get_token(1);
    is_above(state, state.token(token).column)
}

/// `JunctionListContext.isNewBullet`.
pub(super) fn is_new_bullet(state: &mut State) -> bool {
    let token = state.get_token(1);
    let token = state.token(token);
    state
        .junctions
        .last()
        .is_some_and(|junction| junction.column == token.column && junction.kind == token.kind)
}

/// `TLAplusParser.caseSep`.
pub(super) fn is_case_separator(state: &mut State) -> bool {
    state.next_kind_is(&["CASESEP"]) && is_above_current(state)
}

/// The Java code that lets a keyword name a module or a record field.
pub(super) fn set_field_name(state: &mut State) {
    let token = state.get_token(1);
    if FIELD_NAME_KINDS.contains(state.kind_of(token)) {
        state.tokens[token].kind = kind("IDENTIFIER");
    }
}

/// The OpArgs node that a PrimitiveExp's heirs end with, directly or in their last `!`
/// extension.
pub(super) fn arguments(heirs: &[std::rc::Rc<Node>]) -> Option<&Node> {
    let last = heirs.last()?;
    let node = match last.kind {
        "BangExt" => last.heirs.last()?,
        _ => last,
    };
    (node.kind == "OpArgs").then_some(&**node)
}

/// `TLAplusParser.isLabel`: whether a node is an identifier, or an operator applied to
/// identifiers.
pub(super) fn is_label(node: &Node) -> bool {
    if node.kind == "GeneralId" {
        return true;
    }
    let op_args = match node.kind {
        "OpApplication" => arguments(&node.heirs),
        _ => None,
    };
    op_args.is_some_and(|op_args| {
        op_args
            .heirs
            .iter()
            .enumerate()
            .all(|(index, argument)| index % 2 == 0 || argument.kind == "GeneralId")
    })
}

/// The first node below `node`, stopping at junction lists, that does not start to the right
/// of the current junction list's bullet: what `TLAplusParser.checkIndentation` reports.
pub(super) fn misindented<'a>(state: &State, node: &'a Node) -> Option<&'a Node> {
    for child in &node.heirs {
        if child.kind == "Junctions" {
            continue;
        }
        if !is_above(state, state.token(child.first).column) {
            return Some(child);
        }
        if let Some(found) = misindented(state, child) {
            return Some(found);
        }
    }
    None
}

/// `TLAplusParser.belchDEF`, which inserts a DEFBREAK token before the left-hand side of the
/// next definition. It reverses the links of the tokens it walks over, so that `next` leads
/// back toward the definition's start, and restores them when done.
pub(super) fn belch_def(state: &mut State) {
    let stops: Vec<Kind> =
        ["EOF", "THEOREM", "PROPOSITION", "ASSUMPTION", "END_MODULE"].map(kind).to_vec();
    let is = |token: &Token, names: &[&str]| names.iter().any(|name| token.kind == kind(name));
    let is_operator = |token: &Token| OPERATOR_KINDS.contains(token.kind);
    let identifier = kind("IDENTIFIER");
    let mut previous = Some(state.token);
    let mut current = state.next(state.token);
    state.tokens[state.token].next = None;
    let mut next = state.next(current);
    state.tokens[current].next = previous;
    while !stops.contains(&state.kind_of(next))
        && !is(state.token(current), &["THEOREM", "PROPOSITION"])
    {
        if is(state.token(current), &["DEF"]) {
            let mut head = previous;
            let tokens = &state.tokens;
            let at = |index: Option<usize>| index.map(|index| &tokens[index]);
            let previous_token = &tokens[previous.expect("a token precedes ==")];
            if is(previous_token, &["RBR", "RSB"]) {
                let mut depth = 1;
                let mut index = previous.expect("a token precedes ==");
                while let Some(back) = tokens[index].next {
                    index = back;
                    let is_open = is(&tokens[index], &["LBR", "LSB"]);
                    if is_open && depth == 1 {
                        break;
                    }
                    if is_open && depth > 1 {
                        depth -= 1;
                    }
                    if is(&tokens[index], &["RBR", "RSB"]) {
                        depth += 1;
                    }
                }
                head = match tokens[index].next {
                    None => None,
                    Some(back) if tokens[back].kind == identifier => Some(back),
                    Some(_) => Some(index),
                };
            } else if previous_token.kind == identifier {
                let operator = previous_token.next;
                if let Some(operator_token) = at(operator)
                    && is_operator(operator_token)
                {
                    let after = at(operator_token.next);
                    let is_postfix = POSTFIX_KINDS.contains(operator_token.kind);
                    let is_infix = INFIX_KINDS.contains(operator_token.kind);
                    if !is_postfix
                        && (!is_infix || after.is_some_and(|after| after.kind == identifier))
                    {
                        head = match after.is_some_and(|after| after.kind == kind("SUBSTITUTE")) {
                            true => previous,
                            false if is_infix => operator_token.next,
                            false => operator,
                        };
                    }
                }
            } else if is_operator(previous_token) {
                head = previous_token.next;
            }
            if let Some(head) = head {
                let after = state.tokens[head].next;
                if after.is_none_or(|after| state.kind_of(after) != kind("DEFBREAK")) {
                    let token = &state.tokens[head];
                    let defbreak = Token {
                        kind: kind("DEFBREAK"),
                        image: "Beginning of definition".to_owned(),
                        line: token.line,
                        column: token.column,
                        next: after,
                    };
                    state.tokens.push(defbreak);
                    let index = state.tokens.len() - 1;
                    state.tokens[head].next = Some(index);
                }
            }
            break;
        }
        previous = Some(current);
        current = next;
        next = state.next(current);
        state.tokens[current].next = previous;
    }
    while let Some(back) = previous {
        state.tokens[current].next = Some(next);
        next = current;
        current = back;
        previous = state.tokens[current].next;
    }
    state.tokens[current].next = Some(next);
}

/// `TLAplusParser.matchFcnConst`: whether the next tokens are `<< ... >> \in` or a list of
/// identifiers followed by `\in`.
pub(super) fn match_fcn_const(state: &mut State) -> bool {
    let mut token = state.get_token(1);
    let (identifier, comma, is_in) = (kind("IDENTIFIER"), kind("COMMA"), kind("IN"));
    if state.kind_of(token) == kind("LAB") {
        let mut depth = 1;
        while depth != 0 {
            token = state.next(token);
            match state.kind_of(token) {
                found if found == kind("LAB") => depth += 1,
                found if found == kind("RAB") => depth -= 1,
                found if found == kind("EOF") => return false,
                _ => {}
            }
        }
        let next = state.next(token);
        return state.kind_of(next) == is_in;
    }
    if state.kind_of(token) != identifier {
        return false;
    }
    token = state.next(token);
    while state.kind_of(token) == comma {
        token = state.next(token);
        if state.kind_of(token) != identifier {
            return false;
        }
        token = state.next(token);
    }
    state.kind_of(token) == is_in
}

/// `TLAplusParser.levelOfProofStepLexeme`: -1 for `<*>` and -2 for `<+>`.
fn step_level(token: &Token) -> i64 {
    let chars = token.image.chars().skip(1);
    match chars.clone().next() {
        Some('*') => -1,
        Some('+') => -2,
        _ => chars.take_while(char::is_ascii_digit).collect::<String>().parse().unwrap_or(-3),
    }
}

/// `TLAplusParser.getProofLevel`. `TLAplusParser`'s `proofDepth` is the length of
/// `proof_levels` less 1.
pub(super) fn proof_level(state: &State) -> i64 {
    state.proof_levels.last().copied().unwrap_or(-1)
}

pub(super) fn begins_proof(state: &mut State) -> bool {
    let token = state.get_token(1);
    let token = state.token(token).clone();
    let mut chars = token.image.chars();
    let second = chars.nth(1);
    match second {
        None => return false,
        Some('*') => return state.proof_levels.is_empty(),
        Some('+') => return true,
        Some(_) => {}
    }
    let steps =
        ["ProofStepLexeme", "BareLevelLexeme", "UnnumberedStepLexeme", "ProofStepDotLexeme"];
    if state.next_kind_is(&steps) {
        if state.proof_levels.is_empty() {
            return true;
        }
        return proof_level(state) >= 0 && step_level(&token) > proof_level(state);
    }
    state.next_kind_is(&["BY", "PROOF", "OBVIOUS", "OMITTED"])
}

/// `TLAplusParser.correctLevel`, which also sets the level of a proof from its first step.
fn is_correct_level(state: &mut State, token: usize) -> bool {
    let level = step_level(state.token(token));
    let depth = state.proof_levels.len() - 1;
    let outer_level = depth.checked_sub(1).map_or(-1, |outer| state.proof_levels[outer]);
    let is_first_step = state.proof_levels[depth] < 0;
    if is_first_step {
        state.proof_levels[depth] = if level < 0 { outer_level + 1 } else { level };
    }
    match level {
        -1 => true,
        -2 => is_first_step,
        _ if is_first_step => level > outer_level,
        _ => state.proof_levels[depth] == level,
    }
}

pub(super) fn check_step_level(problem: &'static str) -> Unit {
    action(move |state| {
        let token = state.token;
        (!is_correct_level(state, token))
            .then(|| format!("{}: {problem}", state.location(token, token)))
    })
}
