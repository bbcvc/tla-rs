//! The token kinds of SANY's grammar, `javacc/tla+.jj`, in the order of the
//! `TLAplusParserConstants` that JavaCC generates from it.

use std::collections::{HashMap, HashSet};
use std::sync::LazyLock;

pub(super) type Kind = u16;

/// The token kinds, each with the literal images that produce it. JavaCC breaks a tie between
/// matches of the same length by this order. The anonymous infix operators share the name
/// `infix`, which no production looks up.
const KINDS: &[(&str, &[&str])] = &[
    ("EOF", &[]),
    ("BEGIN_PRAGMA", &["--->"]),
    ("_BM1", &[]),
    ("NUMBER", &[]),
    ("_BM2", &[]),
    ("_BM0", &[]),
    ("SEPARATOR", &[]),
    ("END_MODULE", &[]),
    ("ACTION", &["ACTION", "ACTIONS"]),
    ("ASSUME", &["ASSUME"]),
    ("BOXASSUME", &["[]ASSUME"]),
    ("ASSUMPTION", &["ASSUMPTION", "AXIOM"]),
    ("CASE", &["CASE"]),
    ("CHOOSE", &["CHOOSE"]),
    ("CONSTANT", &["CONSTANT", "CONSTANTS"]),
    ("ELSE", &["ELSE"]),
    ("EXCEPT", &["EXCEPT"]),
    ("EXISTS", &["\\E", "\\exists", "∃"]),
    ("EXTENDS", &["EXTENDS"]),
    ("FORALL", &["\\A", "\\forall", "∀"]),
    ("IF", &["IF"]),
    ("INSTANCE", &["INSTANCE"]),
    ("LET", &["LET"]),
    ("LETIN", &["IN"]),
    ("LOCAL", &["LOCAL"]),
    ("MODULE", &["MODULE"]),
    ("NEW", &["NEW"]),
    ("OTHER", &["OTHER"]),
    ("PROPOSITION", &["PROPOSITION", "LEMMA", "COROLLARY"]),
    ("SF", &["SF_"]),
    ("T_EXISTS", &["\\EE"]),
    ("T_FORALL", &["\\AA"]),
    ("THEN", &["THEN"]),
    ("BY", &["BY"]),
    ("ONLY", &["ONLY"]),
    ("DEFINE", &["DEFINE"]),
    ("DF", &["DEF", "DEFS"]),
    ("THEOREM", &["THEOREM"]),
    ("USE", &["USE"]),
    ("HIDE", &["HIDE"]),
    ("HAVE", &["HAVE"]),
    ("OBVIOUS", &["OBVIOUS"]),
    ("OMITTED", &["OMITTED"]),
    ("LAMBDA", &["LAMBDA"]),
    ("TAKE", &["TAKE"]),
    ("PROOF", &["PROOF"]),
    ("PROVE", &["PROVE"]),
    ("BOXPROVE", &["[]PROVE"]),
    ("QED", &["QED"]),
    ("RECURSIVE", &["RECURSIVE"]),
    ("STATE", &["STATE"]),
    ("TEMPORAL", &["TEMPORAL", "TEMPORALS"]),
    ("PICK", &["PICK"]),
    ("WITNESS", &["WITNESS"]),
    ("SUFFICES", &["SUFFICES"]),
    ("VARIABLE", &["VARIABLE", "VARIABLES"]),
    ("WF", &["WF_"]),
    ("WITH", &["WITH"]),
    ("COMMA", &[","]),
    ("COLON", &[":"]),
    ("COLONCOLON", &["::", "∷"]),
    ("DOT", &["."]),
    ("US", &["_"]),
    ("DEF", &["==", "≜"]),
    ("LBR", &["("]),
    ("RBR", &[")"]),
    ("DEFBREAK", &["-|-"]),
    ("LSB", &["["]),
    ("ARSB", &["]_"]),
    ("RSB", &["]"]),
    ("LBC", &["{"]),
    ("RBC", &["}"]),
    ("LAB", &["<<", "⟨"]),
    ("ARAB", &[">>_", "⟩_"]),
    ("RAB", &[">>", "⟩"]),
    ("BANG", &["!"]),
    ("ARROW", &["->", "→"]),
    ("SUBSTITUTE", &["<-", "←"]),
    ("MAPTO", &["|->", "↦"]),
    ("NUMBER_LITERAL", &[]),
    ("STRING_LITERAL", &[]),
    ("BAND", &[]),
    ("BOR", &[]),
    ("op_57", &["'"]),
    ("op_68", &["^+", "⁺"]),
    ("op_69", &["^*"]),
    ("op_70", &["^#"]),
    ("op_76", &["-."]),
    ("op_26", &["\\lnot", "¬"]),
    ("op_29", &["\\neg"]),
    ("op_58", &["~"]),
    ("CASESEP", &["[]", "□"]),
    ("op_61", &["<>", "◇"]),
    ("op_112", &["ENABLED"]),
    ("op_113", &["UNCHANGED"]),
    ("op_114", &["SUBSET"]),
    ("op_115", &["UNION"]),
    ("op_116", &["DOMAIN"]),
    ("op_1", &["//"]),
    ("AND", &["/\\", "∧"]),
    ("op_3", &["/="]),
    ("op_4", &["/"]),
    ("OR", &["\\/", "∨"]),
    ("infix", &["\\approx"]),
    ("infix", &["\\asymp"]),
    ("infix", &["\\bigcirc"]),
    ("infix", &["\\bullet"]),
    ("infix", &["\\cap"]),
    ("infix", &["\\cdot"]),
    ("infix", &["\\circ"]),
    ("infix", &["\\cong"]),
    ("infix", &["\\cup"]),
    ("infix", &["\\div"]),
    ("infix", &["\\doteq"]),
    ("infix", &["\\equiv"]),
    ("infix", &["\\geq"]),
    ("infix", &["\\gg"]),
    ("IN", &["\\in", "∈"]),
    ("infix", &["\\intersect"]),
    ("infix", &["\\union"]),
    ("infix", &["\\land"]),
    ("infix", &["\\leq"]),
    ("infix", &["\\ll"]),
    ("infix", &["\\lor"]),
    ("infix", &["\\o"]),
    ("infix", &["\\odot"]),
    ("infix", &["\\ominus"]),
    ("infix", &["\\oplus"]),
    ("infix", &["\\oslash"]),
    ("infix", &["\\otimes"]),
    ("infix", &["\\prec"]),
    ("infix", &["\\preceq"]),
    ("infix", &["\\propto"]),
    ("infix", &["\\sim"]),
    ("infix", &["\\simeq"]),
    ("infix", &["\\sqcap"]),
    ("infix", &["\\sqcup"]),
    ("infix", &["\\sqsubset"]),
    ("infix", &["\\sqsupset"]),
    ("infix", &["\\sqsubseteq"]),
    ("infix", &["\\sqsupseteq"]),
    ("infix", &["\\star"]),
    ("infix", &["\\subset"]),
    ("infix", &["\\subseteq"]),
    ("infix", &["\\succ"]),
    ("infix", &["\\succeq"]),
    ("infix", &["\\supset"]),
    ("infix", &["\\supseteq"]),
    ("infix", &["\\uplus"]),
    ("infix", &["\\wr"]),
    ("infix", &["\\"]),
    ("infix", &["~>"]),
    ("infix", &["=>"]),
    ("infix", &["=<"]),
    ("infix", &["=|"]),
    ("EQUALS", &["="]),
    ("infix", &["##"]),
    ("infix", &["#"]),
    ("infix", &["^^"]),
    ("infix", &["^"]),
    ("infix", &["--"]),
    ("infix", &["-|"]),
    ("infix", &["-+->"]),
    ("op_77", &["-"]),
    ("infix", &["**"]),
    ("infix", &["*"]),
    ("infix", &["++"]),
    ("infix", &["+"]),
    ("infix", &["<=>"]),
    ("infix", &["<:"]),
    ("infix", &["<="]),
    ("infix", &["<"]),
    ("infix", &[">="]),
    ("infix", &[">"]),
    ("infix", &["..."]),
    ("infix", &[".."]),
    ("infix", &["||"]),
    ("infix", &["|"]),
    ("infix", &["|-"]),
    ("infix", &["|="]),
    ("infix", &["&&"]),
    ("infix", &["&"]),
    ("infix", &["$$"]),
    ("infix", &["$"]),
    ("infix", &["??"]),
    ("infix", &["%%"]),
    ("infix", &["%"]),
    ("infix", &["@@"]),
    ("infix", &["!!"]),
    ("infix", &[":>"]),
    ("infix", &[":="]),
    ("infix", &["::="]),
    ("infix", &["(+)"]),
    ("infix", &["(-)"]),
    ("infix", &["(.)"]),
    ("infix", &["(/)"]),
    ("infix", &["(\\X)"]),
    ("infix", &["\\notin"]),
    ("infix", &["≈"]),
    ("infix", &["≔"]),
    ("infix", &["≍"]),
    ("infix", &["◯"]),
    ("infix", &["⩴"]),
    ("infix", &["●"]),
    ("infix", &["∩"]),
    ("infix", &["⋅"]),
    ("infix", &["∘"]),
    ("infix", &["≅"]),
    ("infix", &["∪"]),
    ("infix", &["÷"]),
    ("infix", &["≐"]),
    ("infix", &["‥"]),
    ("infix", &["…"]),
    ("infix", &["≡"]),
    ("infix", &["‼"]),
    ("infix", &["≥"]),
    ("infix", &["≫"]),
    ("infix", &["⇔"]),
    ("infix", &["⇒"]),
    ("infix", &["⫤"]),
    ("infix", &["↝"]),
    ("infix", &["≤"]),
    ("infix", &["≪"]),
    ("infix", &["⊣"]),
    ("infix", &["≠"]),
    ("infix", &["∉"]),
    ("infix", &["⊙"]),
    ("infix", &["⊖"]),
    ("infix", &["⊕"]),
    ("infix", &["⊘"]),
    ("infix", &["⊗"]),
    ("infix", &["⇸"]),
    ("infix", &["≺"]),
    ("infix", &["⪯"]),
    ("infix", &["∝"]),
    ("infix", &["⁇"]),
    ("infix", &["⊨"]),
    ("infix", &["⊢"]),
    ("infix", &["∼"]),
    ("infix", &["≃"]),
    ("infix", &["⊓"]),
    ("infix", &["⊔"]),
    ("infix", &["⊏"]),
    ("infix", &["⊑"]),
    ("infix", &["⊐"]),
    ("infix", &["⊒"]),
    ("infix", &["⋆"]),
    ("infix", &["⊂"]),
    ("infix", &["⊆"]),
    ("infix", &["≻"]),
    ("infix", &["⪰"]),
    ("infix", &["⊃"]),
    ("infix", &["⊇"]),
    ("infix", &["×"]),
    ("infix", &["⊎"]),
    ("infix", &["‖"]),
    ("infix", &["≀"]),
    ("infix", &["\\times"]),
    ("op_119", &["\\X"]),
    ("IDENTIFIER", &[]),
    ("ProofStepLexeme", &[]),
    ("ProofImplicitStepLexeme", &[]),
    ("ProofStepDotLexeme", &[]),
    ("BareLevelLexeme", &[]),
    ("UnnumberedStepLexeme", &[]),
];

struct Table {
    by_name: HashMap<&'static str, Kind>,
    literals: HashMap<&'static str, Kind>,
    /// Every proper prefix of a literal, which JavaCC's token manager reads on from.
    prefixes: HashSet<String>,
    longest: usize,
}

static TABLE: LazyLock<Table> = LazyLock::new(|| {
    let mut by_name = HashMap::new();
    let mut literals = HashMap::new();
    for (index, (name, images)) in KINDS.iter().enumerate() {
        let kind = index as Kind;
        by_name.entry(*name).or_insert(kind);
        for image in *images {
            literals.insert(*image, kind);
        }
    }
    let prefixes = literals
        .keys()
        .flat_map(|image| {
            let chars: Vec<char> = image.chars().collect();
            (1..chars.len()).map(move |length| chars[..length].iter().collect())
        })
        .collect();
    let longest = literals.keys().map(|image| image.chars().count()).max().unwrap_or(0);
    Table { by_name, literals, prefixes, longest }
});

/// The number of token kinds.
pub(super) const COUNT: usize = KINDS.len();

/// The kind named `name`.
pub(super) fn kind(name: &str) -> Kind {
    match TABLE.by_name.get(name) {
        Some(kind) => *kind,
        None => panic!("SANY has no token kind {name}"),
    }
}

pub(super) fn name(kind: Kind) -> &'static str {
    KINDS[kind as usize].0
}

/// The kinds from `first` to `last`, both included.
pub(super) fn range(first: &str, last: &str) -> impl Iterator<Item = Kind> {
    kind(first)..=kind(last)
}

/// The kind of the literal `image`, if it is one.
pub(super) fn literal(image: &str) -> Option<Kind> {
    TABLE.literals.get(image).copied()
}

pub(super) fn is_literal_prefix(text: &str) -> bool {
    TABLE.prefixes.contains(text)
}

/// The length in characters of the longest literal.
pub(super) fn longest_literal() -> usize {
    TABLE.longest
}

/// A set of token kinds.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct Kinds([u64; COUNT.div_ceil(64)]);

impl Kinds {
    pub(super) fn of(kinds: impl IntoIterator<Item = Kind>) -> Self {
        let mut set = Self::default();
        for kind in kinds {
            set.insert(kind);
        }
        set
    }

    pub(super) fn insert(&mut self, kind: Kind) {
        self.0[kind as usize / 64] |= 1 << (kind % 64);
    }

    pub(super) fn contains(&self, kind: Kind) -> bool {
        self.0[kind as usize / 64] & (1 << (kind % 64)) != 0
    }

    pub(super) fn union(&mut self, other: &Kinds) {
        for (word, other) in self.0.iter_mut().zip(other.0) {
            *word |= other;
        }
    }
}
