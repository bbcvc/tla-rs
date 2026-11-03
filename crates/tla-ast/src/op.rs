/// Defines [`Op`] from one table: variant, tree-sitter-tlaplus node kind, canonical ASCII name.
macro_rules! operators {
    ($($variant:ident = $kind:literal => $name:literal,)*) => {
        /// A prefix, infix, or postfix operator symbol.
        ///
        /// Synonyms share one variant: `#` and `/=` are both [`Op::Neq`].
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub enum Op {
            $($variant,)*
        }

        impl Op {
            /// Maps a tree-sitter-tlaplus node kind, such as `"cup"`, to its operator.
            pub fn from_syntax_kind(kind: &str) -> Option<Self> {
                match kind {
                    $($kind => Some(Self::$variant),)*
                    _ => None,
                }
            }

            /// The canonical ASCII spelling, which is also the name a user definition of the
            /// operator is stored under.
            pub fn name(self) -> &'static str {
                match self {
                    $(Self::$variant => $name,)*
                }
            }
        }
    };
}

operators! {
    // Infix operators.
    Amp = "amp" => "&",
    AmpAmp = "ampamp" => "&&",
    And = "land" => "/\\",
    Approx = "approx" => "\\approx",
    Assign = "assign" => ":=",
    Asymp = "asymp" => "\\asymp",
    BigCirc = "bigcirc" => "\\bigcirc",
    BnfRule = "bnf_rule" => "::=",
    Bullet = "bullet" => "\\bullet",
    Cap = "cap" => "\\cap",
    Cdot = "cdot" => "\\cdot",
    Circ = "circ" => "\\o",
    Compose = "compose" => "@@",
    Cong = "cong" => "\\cong",
    Cup = "cup" => "\\cup",
    Div = "div" => "\\div",
    Dol = "dol" => "$",
    DolDol = "doldol" => "$$",
    DotEq = "doteq" => "\\doteq",
    Ellipsis = "dots_3" => "...",
    Eq = "eq" => "=",
    Equiv = "equiv" => "\\equiv",
    Excl = "excl" => "!!",
    Geq = "geq" => "\\geq",
    Gg = "gg" => "\\gg",
    Gt = "gt" => ">",
    HashHash = "hashhash" => "##",
    Iff = "iff" => "<=>",
    Implies = "implies" => "=>",
    In = "in" => "\\in",
    LdTtile = "ld_ttile" => "=|",
    LeadsTo = "leads_to" => "~>",
    Leq = "leq" => "\\leq",
    Ll = "ll" => "\\ll",
    LsTtile = "ls_ttile" => "-|",
    Lt = "lt" => "<",
    MapFrom = "map_from" => "<:",
    MapTo = "map_to" => ":>",
    Minus = "minus" => "-",
    MinusMinus = "minusminus" => "--",
    Mod = "mod" => "%",
    ModMod = "modmod" => "%%",
    Mul = "mul" => "*",
    MulMul = "mulmul" => "**",
    Neq = "neq" => "/=",
    NotIn = "notin" => "\\notin",
    Odot = "odot" => "\\odot",
    Ominus = "ominus" => "\\ominus",
    Oplus = "oplus" => "\\oplus",
    Or = "lor" => "\\/",
    Oslash = "oslash" => "\\oslash",
    Otimes = "otimes" => "\\otimes",
    Plus = "plus" => "+",
    PlusArrow = "plus_arrow" => "-+->",
    PlusPlus = "plusplus" => "++",
    Pow = "pow" => "^",
    PowPow = "powpow" => "^^",
    Prec = "prec" => "\\prec",
    PrecEq = "preceq" => "\\preceq",
    ProperSubset = "subset" => "\\subset",
    ProperSupset = "supset" => "\\supset",
    Propto = "propto" => "\\propto",
    Qq = "qq" => "??",
    Range = "dots_2" => "..",
    RdTtile = "rd_ttile" => "|=",
    RsTtile = "rs_ttile" => "|-",
    SetMinus = "setminus" => "\\",
    Sim = "sim" => "\\sim",
    SimEq = "simeq" => "\\simeq",
    Slash = "slash" => "/",
    SlashSlash = "slashslash" => "//",
    SqCap = "sqcap" => "\\sqcap",
    SqCup = "sqcup" => "\\sqcup",
    SqSubset = "sqsubset" => "\\sqsubset",
    SqSubsetEq = "sqsubseteq" => "\\sqsubseteq",
    SqSupset = "sqsupset" => "\\sqsupset",
    SqSupsetEq = "sqsupseteq" => "\\sqsupseteq",
    Star = "star" => "\\star",
    SubsetEq = "subseteq" => "\\subseteq",
    Succ = "succ" => "\\succ",
    SuccEq = "succeq" => "\\succeq",
    SupsetEq = "supseteq" => "\\supseteq",
    Times = "times" => "\\X",
    Uplus = "uplus" => "\\uplus",
    Vert = "vert" => "|",
    VertVert = "vertvert" => "||",
    Wr = "wr" => "\\wr",
    // Prefix operators.
    Always = "always" => "[]",
    Domain = "domain" => "DOMAIN",
    Enabled = "enabled" => "ENABLED",
    Eventually = "eventually" => "<>",
    Negate = "negative" => "-.",
    Not = "lnot" => "~",
    Powerset = "powerset" => "SUBSET",
    Unchanged = "unchanged" => "UNCHANGED",
    Union = "union" => "UNION",
    // Postfix operators.
    Prime = "prime" => "'",
    SupHash = "sup_hash" => "^#",
    SupPlus = "sup_plus" => "^+",
    SupStar = "asterisk" => "^*",
}

#[cfg(test)]
mod tests {
    use super::Op;

    #[test]
    fn maps_kinds_to_canonical_names() {
        assert_eq!(Op::from_syntax_kind("neq"), Some(Op::Neq));
        assert_eq!(Op::Neq.name(), "/=");
        assert_eq!(Op::from_syntax_kind("negative").map(Op::name), Some("-."));
        assert_eq!(Op::from_syntax_kind("identifier"), None);
    }
}
