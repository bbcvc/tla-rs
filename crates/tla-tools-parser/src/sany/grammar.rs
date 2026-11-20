//! The units SANY's grammar is written in, and the helpers that build them.

use std::collections::HashMap;
use std::sync::{LazyLock, OnceLock};

use super::kinds::{Kind, Kinds, kind};
use super::{Frame, State};

pub(super) type Predicate = Box<dyn Fn(&mut State) -> bool + Send + Sync>;
/// Java code in a production, which may throw a `ParseException` with a message.
pub(super) type Action = Box<dyn Fn(&mut State) -> Option<String> + Send + Sync>;
/// Java code that runs after a production's `epa`.
pub(super) type Exit = Box<dyn Fn(&mut Frame, &mut State) -> Option<String> + Send + Sync>;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Repeat {
    ZeroOrMore,
    OneOrMore,
    Optional,
}

pub(super) enum UnitKind {
    Tokens(Kinds),
    Call(&'static str),
    Sequence(Vec<Unit>),
    /// Alternatives, each a sequence.
    Choice(Vec<Unit>),
    /// A body, which is a sequence.
    Repeat(Repeat, Box<Unit>),
    Action(Action),
    /// A LOOKAHEAD specification. First in a choice's alternative or in a loop's body, it
    /// decides whether to take that expansion. Elsewhere, JavaCC checks only its semantic
    /// part.
    Lookahead {
        amount: i64,
        expansion: Option<Box<Unit>>,
        semantic: Option<Predicate>,
    },
}

pub(super) struct Unit {
    pub(super) kind: UnitKind,
    pub(super) analysis: OnceLock<Analysis>,
}

/// What JavaCC's `ParseEngine.genFirstSet` and `Semanticize.emptyExpansionExists` compute:
/// the tokens an expansion can start with, whether it can match nothing, and whether its start
/// passes a semantic lookahead, which makes JavaCC decide by a `jj_2` call instead of a switch
/// (`jj2LA`).
#[derive(Clone, Copy, Default)]
pub(super) struct Analysis {
    pub(super) first: Kinds,
    pub(super) is_nullable: bool,
    pub(super) has_semantic_start: bool,
}

impl Unit {
    pub(super) fn new(kind: UnitKind) -> Self {
        Self { kind, analysis: OnceLock::new() }
    }

    pub(super) fn sequence(units: Vec<Unit>) -> Self {
        Self::new(UnitKind::Sequence(units))
    }

    /// The units of a sequence, empty for any other unit.
    pub(super) fn units(&self) -> &[Unit] {
        match &self.kind {
            UnitKind::Sequence(units) => units,
            _ => &[],
        }
    }

    /// The lookahead that starts a sequence, if one does.
    pub(super) fn head_lookahead(&self) -> Option<&Unit> {
        self.units().first().filter(|unit| matches!(unit.kind, UnitKind::Lookahead { .. }))
    }

    pub(super) fn analysis(&'static self) -> &'static Analysis {
        self.analysis.get_or_init(|| analyze(self))
    }
}

fn analyze(unit: &'static Unit) -> Analysis {
    let mut analysis = Analysis { is_nullable: true, ..Analysis::default() };
    let mut add = |inner: &'static Unit| {
        let inner = inner.analysis();
        analysis.first.union(&inner.first);
        analysis.has_semantic_start |= inner.has_semantic_start;
        inner.is_nullable
    };
    match &unit.kind {
        UnitKind::Tokens(kinds) => {
            return Analysis { first: *kinds, is_nullable: false, has_semantic_start: false };
        }
        UnitKind::Call(name) => return *production(name).body.analysis(),
        UnitKind::Lookahead { semantic, .. } => {
            return Analysis { has_semantic_start: semantic.is_some(), ..analysis };
        }
        UnitKind::Action(_) => {}
        UnitKind::Sequence(units) => {
            let is_nullable = units.iter().enumerate().all(|(index, inner)| {
                (index == 0 && matches!(inner.kind, UnitKind::Lookahead { .. })) || add(inner)
            });
            let head = units.first().map(|head| &head.kind);
            let is_semantic = matches!(head, Some(UnitKind::Lookahead { semantic: Some(_), .. }));
            analysis.has_semantic_start |= is_semantic;
            analysis.is_nullable = is_nullable;
        }
        UnitKind::Choice(alternatives) => {
            let nullables: Vec<bool> = alternatives.iter().map(&mut add).collect();
            analysis.is_nullable = nullables.into_iter().any(|nullable| nullable);
        }
        UnitKind::Repeat(repeat, body) => {
            analysis.is_nullable = add(body) || *repeat != Repeat::OneOrMore;
        }
    }
    analysis
}

/// A production of the grammar.
pub(super) struct Production {
    /// The name `TLAplusParser.bpa` pushes on the message stack, if the production calls it.
    pub(super) message: Option<&'static str>,
    pub(super) body: Unit,
    pub(super) exit: Option<Exit>,
}

static PRODUCTIONS: LazyLock<HashMap<&'static str, Production>> = LazyLock::new(|| {
    let mut productions = HashMap::new();
    super::productions::add(&mut productions);
    super::proofs::add(&mut productions);
    super::expressions::add(&mut productions);
    super::extendable::add(&mut productions);
    productions
});

pub(super) fn production(name: &str) -> &'static Production {
    match PRODUCTIONS.get(name) {
        Some(production) => production,
        None => panic!("SANY's grammar has no production {name}"),
    }
}

/// A token kind in angle brackets, as `<COMMA>`, or a production's name.
impl From<&'static str> for Unit {
    fn from(part: &'static str) -> Self {
        match part.strip_prefix('<').and_then(|part| part.strip_suffix('>')) {
            Some(name) => tokens([kind(name)]),
            None => Unit::new(UnitKind::Call(part)),
        }
    }
}

impl From<Action> for Unit {
    fn from(action: Action) -> Self {
        Unit::new(UnitKind::Action(action))
    }
}

pub(super) fn tokens(kinds: impl IntoIterator<Item = Kind>) -> Unit {
    Unit::new(UnitKind::Tokens(Kinds::of(kinds)))
}

/// Alternatives, each made a sequence if it is not one.
pub(super) fn choice_of(alternatives: Vec<Unit>) -> Unit {
    let alternatives = alternatives
        .into_iter()
        .map(|unit| match unit.kind {
            UnitKind::Sequence(_) => unit,
            _ => Unit::sequence(vec![unit]),
        })
        .collect();
    Unit::new(UnitKind::Choice(alternatives))
}

pub(super) fn repeat(repeat: Repeat, units: Vec<Unit>) -> Unit {
    Unit::new(UnitKind::Repeat(repeat, Box::new(Unit::sequence(units))))
}

macro_rules! seq {
    ($($part:expr),* $(,)?) => {
        $crate::sany::grammar::Unit::sequence(vec![$($crate::sany::grammar::Unit::from($part)),*])
    };
}

macro_rules! choice {
    ($($part:expr),* $(,)?) => {
        $crate::sany::grammar::choice_of(vec![$($crate::sany::grammar::Unit::from($part)),*])
    };
}

macro_rules! zero_or_more {
    ($($part:expr),* $(,)?) => {
        $crate::sany::grammar::repeat(
            $crate::sany::grammar::Repeat::ZeroOrMore,
            vec![$($crate::sany::grammar::Unit::from($part)),*],
        )
    };
}

macro_rules! one_or_more {
    ($($part:expr),* $(,)?) => {
        $crate::sany::grammar::repeat(
            $crate::sany::grammar::Repeat::OneOrMore,
            vec![$($crate::sany::grammar::Unit::from($part)),*],
        )
    };
}

macro_rules! optional {
    ($($part:expr),* $(,)?) => {
        $crate::sany::grammar::repeat(
            $crate::sany::grammar::Repeat::Optional,
            vec![$($crate::sany::grammar::Unit::from($part)),*],
        )
    };
}

pub(super) use {choice, one_or_more, optional, seq, zero_or_more};

/// JavaCC's amount for a LOOKAHEAD that gives an expansion but no amount.
const UNBOUNDED_AMOUNT: i64 = 2147483647;

/// `LOOKAHEAD(amount)`.
pub(super) fn lookahead_amount(amount: i64) -> Unit {
    Unit::new(UnitKind::Lookahead { amount, expansion: None, semantic: None })
}

/// `LOOKAHEAD(amount, expansion, {semantic})`, without an amount if it is 0.
pub(super) fn lookahead(amount: i64, expansion: Option<Unit>, semantic: Option<Predicate>) -> Unit {
    let amount = match (amount, &expansion) {
        (0, Some(_)) => UNBOUNDED_AMOUNT,
        _ => amount,
    };
    let expansion = expansion.map(|unit| match unit.kind {
        UnitKind::Sequence(_) => Box::new(unit),
        _ => Box::new(Unit::sequence(vec![unit])),
    });
    Unit::new(UnitKind::Lookahead { amount, expansion, semantic })
}

/// `LOOKAHEAD(expansion)`.
pub(super) fn lookahead_expansion(expansion: Unit) -> Unit {
    lookahead(0, Some(expansion), None)
}

/// `LOOKAHEAD({semantic})`.
pub(super) fn lookahead_semantic(
    semantic: impl Fn(&mut State) -> bool + Send + Sync + 'static,
) -> Unit {
    lookahead(0, None, Some(Box::new(semantic)))
}

/// `LOOKAHEAD(expansion, {semantic})`.
pub(super) fn lookahead_both(
    expansion: Unit,
    semantic: impl Fn(&mut State) -> bool + Send + Sync + 'static,
) -> Unit {
    lookahead(0, Some(expansion), Some(Box::new(semantic)))
}

pub(super) fn action(run: impl Fn(&mut State) -> Option<String> + Send + Sync + 'static) -> Unit {
    Unit::new(UnitKind::Action(Box::new(run)))
}

/// Java code that sets the `expecting` message.
pub(super) fn expect(expecting: &'static str) -> Unit {
    action(move |state| {
        state.expecting = expecting;
        None
    })
}
