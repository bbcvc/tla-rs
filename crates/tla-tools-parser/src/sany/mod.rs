//! The report SANY's parser, `TLAplusParser`, gives for a module it fails to parse, ported
//! from tla-ts's `src/sany/parse-error.ts`.
//!
//! This interprets the grammar of `javacc/tla+.jj` the way the code JavaCC generates from it
//! runs: the productions, their lookahead specifications, and the semantic actions that steer
//! parsing or set the `expecting` message. `TLAplusParser.msgStackToString` prints that
//! message, the token the parser failed at, and the productions it was in, so the interpreter
//! must fail at the same token, in the same productions, and must look as far ahead as
//! JavaCC's `jj_rescan_token` does.

mod engine;
mod expressions;
mod extendable;
mod grammar;
mod kinds;
mod lexer;
mod operators;
mod productions;
mod proofs;
mod semantics;

use std::rc::Rc;

use kinds::{Kind, kind};
use lexer::{Lexer, Token};
use operators::{Operator, StackElement};

/// What SANY reports for a module its lexer or parser rejects: `TLAplusParser`'s report under
/// its `***Parse Error***` heading, or the lexer's `TokenMgrError`. `None` if SANY's parser
/// accepts the module, as it does one whose error SANY finds after parsing.
pub fn parse_error(source: &str) -> Option<String> {
    let mut state = State::new(source);
    let is_parsed = engine::parse_production(&mut state, "CompilationUnit");
    if let Some(error) = state.lexical_error {
        return Some(error);
    }
    match (is_parsed, state.report) {
        (false, Some(report)) => Some(format!("***Parse Error***\n{report}")),
        _ => None,
    }
}

/// A `SyntaxTreeNode`: a token, or what a production matched, which spans from its first
/// token to its last.
#[derive(Debug)]
pub(super) struct Node {
    kind: &'static str,
    heirs: Vec<Rc<Node>>,
    first: usize,
    last: usize,
}

impl Node {
    fn new(kind: &'static str, heirs: Vec<Rc<Node>>) -> Rc<Node> {
        let (first, last) = (heirs[0].first, heirs[heirs.len() - 1].last);
        Rc::new(Node { kind, heirs, first, last })
    }
}

/// The production being parsed: the nodes of what it has matched, and the node it returns if
/// that is not a node of its own kind over them.
#[derive(Default)]
pub(super) struct Frame {
    heirs: Vec<Rc<Node>>,
    node: Option<Rc<Node>>,
}

/// A `jj_2` call, which `jj_rescan_token` scans again if it looked past the current token:
/// JavaCC's `JJCalls`.
#[derive(Clone, Copy)]
struct LookaheadCall {
    generation: i64,
    first: usize,
    amount: i64,
}

/// A junction list being parsed: the kind of its bullet and the bullet's column.
struct Junction {
    kind: Kind,
    column: u32,
}

pub(super) struct State {
    lexer: Lexer,
    lexical_error: Option<String>,
    /// The tokens read, linked by their `next`. The first is a placeholder before the first
    /// token, as JavaCC's `token` starts.
    tokens: Vec<Token>,
    token: usize,
    /// `jj_gen`, which counts consumed tokens, and its value at the last failed `jj_ntk`
    /// switch.
    generation: i64,
    failed_switch_generation: i64,
    scan_position: usize,
    last_position: usize,
    remaining: i64,
    is_looking_ahead: bool,
    is_rescanning: bool,
    farthest_rescan: usize,
    /// The saved `jj_2` calls of each lookahead site, by the address of its expansion, in the
    /// order the sites were first used.
    calls: Vec<(&'static grammar::Unit, Vec<LookaheadCall>)>,
    expecting: &'static str,
    /// The names `TLAplusParser.bpa` pushed, each with the token the production started at.
    messages: Vec<(&'static str, usize)>,
    module_name: Option<String>,
    junctions: Vec<Junction>,
    frames: Vec<Frame>,
    /// `OperatorStack`'s stack of stacks, one for each Expression being parsed.
    operator_stacks: Vec<Vec<StackElement>>,
    last_operator: Option<&'static Operator>,
    proof_levels: Vec<i64>,
    is_terminal_proof: bool,
    /// Whether `FairnessHook` is set, which it is if the last NoOpExtension ended with
    /// arguments.
    is_fairness_hooked: bool,
    is_fairness_parenthesized: Vec<bool>,
    report: Option<String>,
}

impl State {
    fn new(source: &str) -> Self {
        let start =
            Token { kind: kind("EOF"), image: String::new(), line: 0, column: 0, next: None };
        Self {
            lexer: Lexer::new(source),
            lexical_error: None,
            tokens: vec![start],
            token: 0,
            generation: 0,
            failed_switch_generation: -1,
            scan_position: 0,
            last_position: 0,
            remaining: 0,
            is_looking_ahead: false,
            is_rescanning: false,
            farthest_rescan: 0,
            calls: Vec::new(),
            expecting: "nothing",
            messages: Vec::new(),
            module_name: None,
            junctions: Vec::new(),
            frames: Vec::new(),
            operator_stacks: Vec::new(),
            last_operator: None,
            proof_levels: Vec::new(),
            is_terminal_proof: false,
            is_fairness_hooked: false,
            is_fairness_parenthesized: Vec::new(),
            report: None,
        }
    }

    fn token(&self, index: usize) -> &Token {
        &self.tokens[index]
    }

    fn kind_of(&self, index: usize) -> Kind {
        self.tokens[index].kind
    }

    /// The token after `index`, read from the lexer if it hasn't been. After a lexical error,
    /// the parser sees the end of the file.
    fn next(&mut self, index: usize) -> usize {
        if let Some(next) = self.tokens[index].next {
            return next;
        }
        let token = match self.lexer.next_token() {
            Ok(token) => token,
            Err(error) => {
                self.lexical_error.get_or_insert(error);
                Token { kind: kind("EOF"), image: String::new(), line: 0, column: 0, next: None }
            }
        };
        self.tokens.push(token);
        let next = self.tokens.len() - 1;
        self.tokens[index].next = Some(next);
        next
    }

    /// `TLAplusParser.getToken`, which counts from the scan position while a semantic
    /// lookahead runs during a scan.
    fn get_token(&mut self, index: usize) -> usize {
        let mut token = if self.is_looking_ahead { self.scan_position } else { self.token };
        for _ in 0..index {
            token = self.next(token);
        }
        token
    }

    fn next_kind_is(&mut self, names: &[&str]) -> bool {
        let token = self.get_token(1);
        let found = self.kind_of(token);
        names.iter().any(|name| kind(name) == found)
    }

    /// `SyntaxTreeNode.getLocation` for the tokens `first` to `last`, as `Location.toString`
    /// prints it.
    fn location(&self, first: usize, last: usize) -> String {
        let (first, last) = (self.token(first), self.token(last));
        format!(
            "line {}, col {} to line {}, col {} of module {}",
            first.line,
            first.column,
            last.line,
            last.column + last.width() - 1,
            self.module_name.as_deref().unwrap_or("null")
        )
    }

    fn node_location(&self, node: &Node) -> String {
        self.location(node.first, node.last)
    }

    /// The node `offset` nodes back among those of what the production being parsed has
    /// matched.
    fn heir(&self, offset: usize) -> Rc<Node> {
        let heirs = &self.frames.last().expect("a production is being parsed").heirs;
        heirs[heirs.len() - offset].clone()
    }

    fn operator_stack(&mut self) -> &mut Vec<StackElement> {
        self.operator_stacks.last_mut().expect("an Expression is being parsed")
    }
}

#[cfg(test)]
mod tests;
