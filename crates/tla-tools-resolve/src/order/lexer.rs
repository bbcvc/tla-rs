//! SANY's tokens, as tla-ts's `lexer.ts` reads them: the texts SANY interns while it parses a
//! module, in order. Operators carry their canonical spelling, as SANY interns them.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    Identifier,
    Number,
    Decimal,
    String,
    Operator,
    Keyword,
    Step,
    Separator,
    ModuleEnd,
}

#[derive(Clone, Debug)]
pub(super) struct Token {
    pub kind: Kind,
    /// The text: a string's contents, or an operator's canonical spelling.
    pub text: String,
    pub line: usize,
    pub column: usize,
}

const KEYWORDS: &[&str] = &[
    "ACTION",
    "ACTIONS",
    "ASSUME",
    "ASSUMPTION",
    "AXIOM",
    "BY",
    "CASE",
    "CHOOSE",
    "CONSTANT",
    "CONSTANTS",
    "COROLLARY",
    "DEF",
    "DEFINE",
    "DEFS",
    "DOMAIN",
    "ELSE",
    "ENABLED",
    "EXCEPT",
    "EXTENDS",
    "HAVE",
    "HIDE",
    "IF",
    "IN",
    "INSTANCE",
    "LAMBDA",
    "LEMMA",
    "LET",
    "LOCAL",
    "MODULE",
    "NEW",
    "OBVIOUS",
    "OMITTED",
    "ONLY",
    "OTHER",
    "PICK",
    "PROOF",
    "PROPOSITION",
    "PROVE",
    "QED",
    "RECURSIVE",
    "STATE",
    "SUBSET",
    "SUFFICES",
    "TAKE",
    "TEMPORAL",
    "TEMPORALS",
    "THEN",
    "THEOREM",
    "UNCHANGED",
    "UNION",
    "USE",
    "VARIABLE",
    "VARIABLES",
    "WITH",
    "WITNESS",
];

const BACKSLASH_OPERATORS: &[(&str, &str)] = &[
    ("in", "\\in"),
    ("notin", "\\notin"),
    ("subseteq", "\\subseteq"),
    ("subset", "\\subset"),
    ("supseteq", "\\supseteq"),
    ("supset", "\\supset"),
    ("cup", "\\cup"),
    ("union", "\\cup"),
    ("cap", "\\cap"),
    ("intersect", "\\cap"),
    ("X", "\\X"),
    ("times", "\\X"),
    ("o", "\\o"),
    ("circ", "\\o"),
    ("div", "\\div"),
    ("land", "/\\"),
    ("lor", "\\/"),
    ("lnot", "~"),
    ("neg", "~"),
    ("equiv", "<=>"),
    ("leq", "<="),
    ("geq", ">="),
    ("A", "\\A"),
    ("forall", "\\A"),
    ("E", "\\E"),
    ("exists", "\\E"),
    ("AA", "\\AA"),
    ("EE", "\\EE"),
    ("cdot", "\\cdot"),
    ("sqsubseteq", "\\sqsubseteq"),
    ("sqsupseteq", "\\sqsupseteq"),
    ("sqsubset", "\\sqsubset"),
    ("sqsupset", "\\sqsupset"),
    ("sqcap", "\\sqcap"),
    ("sqcup", "\\sqcup"),
    ("oplus", "\\oplus"),
    ("ominus", "\\ominus"),
    ("otimes", "\\otimes"),
    ("oslash", "\\oslash"),
    ("odot", "\\odot"),
    ("uplus", "\\uplus"),
    ("prec", "\\prec"),
    ("preceq", "\\preceq"),
    ("succ", "\\succ"),
    ("succeq", "\\succeq"),
    ("sim", "\\sim"),
    ("simeq", "\\simeq"),
    ("approx", "\\approx"),
    ("cong", "\\cong"),
    ("asymp", "\\asymp"),
    ("doteq", "\\doteq"),
    ("propto", "\\propto"),
    ("wr", "\\wr"),
    ("star", "\\star"),
    ("bullet", "\\bullet"),
    ("bigcirc", "\\bigcirc"),
    ("ll", "\\ll"),
    ("gg", "\\gg"),
];

const SYMBOL_ALIASES: &[(&str, &str)] = &[
    ("/=", "#"),
    ("=<", "<="),
    ("(+)", "\\oplus"),
    ("(-)", "\\ominus"),
    ("(.)", "\\odot"),
    ("(/)", "\\oslash"),
    ("(\\X)", "\\otimes"),
];

/// The symbolic operators, longest first where one starts another.
const SYMBOL_OPERATORS: &[&str] = &[
    "-+->", "(\\X)", "<=>", "|->", "...", "::=", ">>_", "(+)", "(-)", "(.)", "(/)", "==", "=>",
    "=<", "=|", "<<", "<=", "<>", "<-", ">>", ">=", "/\\", "\\/", "/=", "[]", "]_", "|-", "|=",
    "||", "->", "-|", "~>", "..", "::", ":=", ":>", "<:", "@@", "++", "--", "-.", "**", "//", "^^",
    "^+", "^*", "^#", "%%", "##", "&&", "$$", "??", "!!", "=", "<", ">", "/", "[", "]", "(", ")",
    "{", "}", "|", "-", "~", ".", ":", "@", ",", "'", "!", "#", "%", "+", "*", "^", "&", "$", "?",
];

/// The Unicode forms of operators, as their ASCII forms.
const UNICODE_OPERATORS: &[(&str, &str)] = &[
    ("∃", "\\E"),
    ("∀", "\\A"),
    ("∷", "::"),
    ("≜", "=="),
    ("⟨", "<<"),
    ("⟩_", ">>_"),
    ("⟩", ">>"),
    ("→", "->"),
    ("←", "<-"),
    ("↦", "|->"),
    ("⁺", "^+"),
    ("¬", "~"),
    ("□", "[]"),
    ("◇", "<>"),
    ("∧", "/\\"),
    ("∨", "\\/"),
    ("∈", "\\in"),
    ("≈", "\\approx"),
    ("≔", ":="),
    ("≍", "\\asymp"),
    ("◯", "\\bigcirc"),
    ("⩴", "::="),
    ("●", "\\bullet"),
    ("∩", "\\cap"),
    ("⋅", "\\cdot"),
    ("∘", "\\o"),
    ("≅", "\\cong"),
    ("∪", "\\cup"),
    ("÷", "\\div"),
    ("≐", "\\doteq"),
    ("‥", ".."),
    ("…", "..."),
    ("≡", "<=>"),
    ("‼", "!!"),
    ("≥", ">="),
    ("≫", "\\gg"),
    ("⇔", "<=>"),
    ("⇒", "=>"),
    ("⫤", "=|"),
    ("↝", "~>"),
    ("≤", "<="),
    ("≪", "\\ll"),
    ("⊣", "-|"),
    ("≠", "#"),
    ("∉", "\\notin"),
    ("⊙", "\\odot"),
    ("⊖", "\\ominus"),
    ("⊕", "\\oplus"),
    ("⊘", "\\oslash"),
    ("⊗", "\\otimes"),
    ("⇸", "-+->"),
    ("≺", "\\prec"),
    ("⪯", "\\preceq"),
    ("∝", "\\propto"),
    ("⁇", "??"),
    ("⊨", "|="),
    ("⊢", "|-"),
    ("∼", "\\sim"),
    ("≃", "\\simeq"),
    ("⊓", "\\sqcap"),
    ("⊔", "\\sqcup"),
    ("⊏", "\\sqsubset"),
    ("⊑", "\\sqsubseteq"),
    ("⊐", "\\sqsupset"),
    ("⊒", "\\sqsupseteq"),
    ("⋆", "\\star"),
    ("⊂", "\\subset"),
    ("⊆", "\\subseteq"),
    ("≻", "\\succ"),
    ("⪰", "\\succeq"),
    ("⊃", "\\supset"),
    ("⊇", "\\supseteq"),
    ("×", "\\X"),
    ("⊎", "\\uplus"),
    ("‖", "||"),
    ("≀", "\\wr"),
];

const TAB_SIZE: usize = 8;

fn is_identifier_char(char: char) -> bool {
    char.is_ascii_alphanumeric() || char == '_'
}

struct Lexer<'a> {
    source: &'a [char],
    index: usize,
    line: usize,
    line_start: usize,
    module_depth: i32,
    tokens: Vec<Token>,
}

impl Lexer<'_> {
    fn starts_with(&self, prefix: &str, at: usize) -> bool {
        let mut chars = self.source.get(at..).unwrap_or_default().iter();
        prefix.chars().all(|char| chars.next() == Some(&char))
    }

    fn skip_while(&self, mut at: usize, is_match: impl Fn(char) -> bool) -> usize {
        while at < self.source.len() && is_match(self.source[at]) {
            at += 1;
        }
        at
    }

    /// The column of the current character, with tabs to the next multiple of 8.
    fn column(&self) -> usize {
        let width = self.source[self.line_start..self.index].iter().fold(0, |width, &char| {
            if char == '\t' { width + TAB_SIZE - width % TAB_SIZE } else { width + 1 }
        });
        width + 1
    }

    fn push(&mut self, kind: Kind, text: String, length: usize) {
        let column = self.column();
        self.tokens.push(Token { kind, text, line: self.line, column });
        self.index += length;
    }

    fn advance(&mut self, length: usize) {
        for _ in 0..length {
            if self.source.get(self.index) == Some(&'\n') {
                self.line += 1;
                self.line_start = self.index + 1;
            }
            self.index += 1;
        }
    }

    fn error(&self, message: &str) -> String {
        format!("{message} at line {}, column {}", self.line, self.column())
    }

    /// A based numeral such as `\b101`, `\o17`, or `\hFF`, as typed.
    fn based_number(&self) -> Option<usize> {
        if self.source.get(self.index) != Some(&'\\') {
            return None;
        }
        let digits: fn(char) -> bool = match self.source.get(self.index + 1)? {
            'b' | 'B' => |char| char == '0' || char == '1',
            'o' | 'O' => |char| ('0'..='7').contains(&char),
            'h' | 'H' => |char| char.is_ascii_hexdigit(),
            _ => return None,
        };
        let end = self.skip_while(self.index + 2, digits);
        (end > self.index + 2).then_some(end - self.index)
    }

    /// The length of a proof step number such as `<1>a.`, `<+>`, or `<2>*.`.
    fn step(&self) -> usize {
        let at = self.index;
        if self.source[at] != '<' {
            return 0;
        }
        let is_implicit = matches!(self.source.get(at + 1), Some('+' | '*'));
        let level_end = if is_implicit {
            at + 2
        } else {
            self.skip_while(at + 1, |char| char.is_ascii_digit())
        };
        if level_end == at + 1 || self.source.get(level_end) != Some(&'>') {
            return 0;
        }
        let name_end = self.skip_while(level_end + 1, is_identifier_char);
        let is_dash =
            name_end == level_end + 1 && matches!(self.source.get(name_end), Some('*' | '-'));
        self.skip_while(if is_dash { name_end + 1 } else { name_end }, |char| char == '.') - at
    }

    /// The operator at the current character: its canonical text and its length.
    fn operator(&self) -> Option<(String, usize)> {
        let at = self.index;
        if self.source[at] == '\\' && self.source.get(at + 1).is_some_and(char::is_ascii_alphabetic)
        {
            let end = self.skip_while(at + 1, |char| char.is_ascii_alphabetic());
            let word: String = self.source[at + 1..end].iter().collect();
            // Like SANY, read the longest operator the word starts with, so S\used is S \ used.
            for length in (1..=word.len()).rev() {
                if let Some((_, operator)) =
                    BACKSLASH_OPERATORS.iter().find(|(name, _)| *name == &word[..length])
                {
                    return Some(((*operator).to_owned(), length + 1));
                }
            }
            return Some(("\\".to_owned(), 1));
        }
        for width in [2, 1] {
            let candidate: String =
                self.source[at..(at + width).min(self.source.len())].iter().collect();
            if let Some((_, operator)) =
                UNICODE_OPERATORS.iter().find(|(name, _)| *name == candidate)
            {
                return Some(((*operator).to_owned(), width));
            }
        }
        if let Some(symbol) = SYMBOL_OPERATORS.iter().find(|symbol| self.starts_with(symbol, at)) {
            let text = SYMBOL_ALIASES
                .iter()
                .find(|(name, _)| name == symbol)
                .map_or(*symbol, |(_, alias)| alias);
            return Some((text.to_owned(), symbol.chars().count()));
        }
        (self.source[at] == '\\').then(|| ("\\".to_owned(), 1))
    }
}

/// The start of the module header `---- MODULE`.
fn module_header(source: &[char]) -> Option<usize> {
    (0..source.len()).find(|&start| {
        let dashes = source[start..].iter().take_while(|&&char| char == '-').count();
        if dashes < 4 || (start > 0 && source[start - 1] == '-') {
            return false;
        }
        let mut at = start + dashes;
        while matches!(source.get(at), Some(' ' | '\t')) {
            at += 1;
        }
        let word: String = source[at..].iter().take(6).collect();
        word == "MODULE" && !source.get(at + 6).is_some_and(|&char| is_identifier_char(char))
    })
}

/// SANY's tokens of a module and the modules nested in it, up to the end of the first module.
pub(super) fn tokenize(text: &str) -> Result<Vec<Token>, String> {
    let source: Vec<char> = text.chars().collect();
    let header = module_header(&source)
        .ok_or_else(|| "Expected a module header such as ---- MODULE Name ----".to_owned())?;
    let line = 1 + source[..header].iter().filter(|&&char| char == '\n').count();
    let line_start = source[..header].iter().rposition(|&char| char == '\n').map_or(0, |at| at + 1);
    let mut lexer = Lexer {
        source: &source,
        index: header,
        line,
        line_start,
        module_depth: 0,
        tokens: Vec::new(),
    };
    while lexer.index < source.len() {
        let char = source[lexer.index];
        if matches!(char, '\n' | ' ' | '\t' | '\r') {
            lexer.advance(1);
        } else if lexer.starts_with("\\*", lexer.index) {
            let end = lexer.skip_while(lexer.index, |char| char != '\n');
            lexer.advance(end - lexer.index);
        } else if lexer.starts_with("(*", lexer.index) {
            let mut depth = 0;
            loop {
                if lexer.index >= source.len() {
                    return Err(lexer.error("Unterminated comment"));
                }
                if lexer.starts_with("(*", lexer.index) {
                    depth += 1;
                    lexer.advance(2);
                } else if lexer.starts_with("*)", lexer.index) {
                    depth -= 1;
                    lexer.advance(2);
                } else {
                    lexer.advance(1);
                }
                if depth == 0 {
                    break;
                }
            }
        } else if lexer.starts_with("----", lexer.index) {
            let length = lexer.skip_while(lexer.index, |char| char == '-') - lexer.index;
            let rest = lexer.skip_while(lexer.index + length, char::is_whitespace);
            if lexer.starts_with("MODULE", rest) {
                lexer.module_depth += 1;
            }
            lexer.push(Kind::Separator, "----".to_owned(), length);
        } else if lexer.starts_with("====", lexer.index) {
            let length = lexer.skip_while(lexer.index, |char| char == '=') - lexer.index;
            lexer.push(Kind::ModuleEnd, "====".to_owned(), length);
            lexer.module_depth -= 1;
            if lexer.module_depth <= 0 {
                break;
            }
        } else if char == '"' {
            let (line, column) = (lexer.line, lexer.column());
            let mut contents = String::new();
            lexer.advance(1);
            while source.get(lexer.index) != Some(&'"') {
                match source.get(lexer.index) {
                    None | Some('\n' | '\r') => return Err(lexer.error("Unterminated string")),
                    Some('\\') => {
                        let escaped = match source.get(lexer.index + 1) {
                            Some('n') => '\n',
                            Some('t') => '\t',
                            Some('r') => '\r',
                            Some('f') => '\u{c}',
                            Some(&escaped @ ('\\' | '"')) => escaped,
                            _ => return Err(lexer.error("Invalid escape in string")),
                        };
                        contents.push(escaped);
                        lexer.advance(2);
                    }
                    Some(&char) => {
                        contents.push(char);
                        lexer.advance(1);
                    }
                }
            }
            lexer.advance(1);
            lexer.tokens.push(Token { kind: Kind::String, text: contents, line, column });
        } else if let Some(length) = lexer.based_number() {
            let text = source[lexer.index..lexer.index + length].iter().collect();
            lexer.push(Kind::Number, text, length);
        } else if is_identifier_char(char) {
            let end = lexer.skip_while(lexer.index, is_identifier_char);
            let word: String = source[lexer.index..end].iter().collect();
            if word.chars().all(|char| char.is_ascii_digit()) {
                let mut number = word.clone();
                if source.get(end) == Some(&'.')
                    && source.get(end + 1).is_some_and(char::is_ascii_digit)
                {
                    let fraction_end = lexer.skip_while(end + 1, |char| char.is_ascii_digit());
                    number = source[lexer.index..fraction_end].iter().collect();
                }
                let kind = if number.contains('.') { Kind::Decimal } else { Kind::Number };
                let length = number.chars().count();
                lexer.push(kind, number, length);
            } else if !word.chars().any(|char| char.is_ascii_alphabetic()) {
                // A word needs a letter to be a name, so SANY reads one without as underscores
                // and numbers.
                if word.starts_with('_') {
                    lexer.push(Kind::Operator, "_".to_owned(), 1);
                } else {
                    let digits: String = word.chars().take_while(char::is_ascii_digit).collect();
                    let length = digits.len();
                    lexer.push(Kind::Number, digits, length);
                }
            } else if word.starts_with("WF_") || word.starts_with("SF_") {
                lexer.push(Kind::Keyword, word[..3].to_owned(), 3);
            } else {
                let kind = if KEYWORDS.contains(&word.as_str()) {
                    Kind::Keyword
                } else {
                    Kind::Identifier
                };
                let length = word.len();
                lexer.push(kind, word, length);
            }
        } else if matches!(char, 'ℕ' | 'ℤ' | 'ℝ') {
            lexer.push(Kind::Identifier, char.to_string(), 1);
        } else if let length @ 1.. = lexer.step() {
            let text = source[lexer.index..lexer.index + length].iter().collect();
            lexer.push(Kind::Step, text, length);
        } else if let Some((text, length)) = lexer.operator() {
            lexer.push(Kind::Operator, text, length);
        } else {
            return Err(lexer.error(&format!("Unexpected character {char:?}")));
        }
    }
    Ok(lexer.tokens)
}
