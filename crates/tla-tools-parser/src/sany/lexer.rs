//! An emulation of the token manager JavaCC generates for SANY's grammar: the tokens it
//! produces, their kinds, and their positions, and the `TokenMgrError` it throws.

use super::kinds::{self, Kind, kind};

/// A token as the parser links them: `next` is the index of the token after it, once read.
#[derive(Clone, Debug)]
pub(super) struct Token {
    pub(super) kind: Kind,
    pub(super) image: String,
    pub(super) line: u32,
    pub(super) column: u32,
    pub(super) next: Option<usize>,
}

impl Token {
    /// The length of the image as Java counts it, in UTF-16 code units.
    pub(super) fn width(&self) -> u32 {
        self.image.encode_utf16().count() as u32
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Default,
    Pragma,
    Spec,
}

/// A pattern that matches at an offset, giving the length of its longest match there.
type Pattern = fn(&[char], usize) -> usize;

/// A lazy token stream over a module's text.
pub(super) struct Lexer {
    source: Vec<char>,
    lines: Vec<u32>,
    columns: Vec<u32>,
    offset: usize,
    mode: Mode,
}

impl Lexer {
    pub(super) fn new(source: &str) -> Self {
        let source: Vec<char> = source.chars().collect();
        let (lines, columns) = positions(&source);
        Self { source, lines, columns, offset: 0, mode: Mode::Default }
    }

    /// The next token, or SANY's message for the `TokenMgrError` JavaCC's token manager throws
    /// at a character no token continues with, or at the end of the file in a comment.
    pub(super) fn next_token(&mut self) -> Result<Token, String> {
        match self.mode {
            Mode::Default => return Ok(self.skipping_token(DEFAULT_PATTERNS)),
            Mode::Pragma => return Ok(self.skipping_token(PRAGMA_PATTERNS)),
            Mode::Spec => {}
        }
        while self.offset < self.source.len() {
            let offset = self.offset;
            let char = self.source[offset];
            if matches!(char, ' ' | '\t' | '\n' | '\r') {
                self.offset += 1;
            } else if self.starts_with(offset, "(*") || self.starts_with(offset, "\\*") {
                self.skip_comment()?;
            } else {
                let (kind, length) = self.spec_token(offset);
                if length == 0 {
                    // JavaCC reads on while a token could continue, and one more character.
                    let prefix = self.token_prefix(offset);
                    let end = (offset + prefix + 1).min(self.source.len());
                    let after = match end < self.source.len() {
                        true => prefix,
                        false if end - offset > 1 => end - offset,
                        false => 0,
                    };
                    let after: String = self.source[offset..offset + after].iter().collect();
                    return Err(self.lexical_error(offset, end, &after));
                }
                self.offset += length;
                return Ok(self.token(kind, offset, length));
            }
        }
        Ok(self.end_of_file())
    }

    fn starts_with(&self, offset: usize, text: &str) -> bool {
        text.chars().enumerate().all(|(index, char)| self.source.get(offset + index) == Some(&char))
    }

    fn token(&self, kind: Kind, start: usize, length: usize) -> Token {
        Token {
            kind,
            image: self.source[start..start + length].iter().collect(),
            line: self.lines.get(start).copied().unwrap_or(0),
            column: self.columns.get(start).copied().unwrap_or(0),
            next: None,
        }
    }

    /// JavaCC places the end of the file at the file's last character.
    fn end_of_file(&self) -> Token {
        let last = self.source.len().wrapping_sub(1);
        Token {
            kind: kind("EOF"),
            image: String::new(),
            line: self.lines.get(last).copied().unwrap_or(0),
            column: self.columns.get(last).copied().unwrap_or(0),
            next: None,
        }
    }

    /// The lexer read the characters from `start` to `end`, and `TLAplusParser.parse` reports
    /// the end of the file in a token that starts on an earlier line as an open comment.
    fn lexical_error(&self, start: usize, end: usize, after: &str) -> String {
        let index = end - 1;
        let (line, column) = (self.lines[index], self.columns[index]);
        if end < self.source.len() {
            return format_lexical_error(line, column, Some(self.source[index]), after);
        }
        if self.lines[start] != line {
            return format!(
                "Lexical {{error: EOF reached, possibly open comment starting around line {}",
                self.lines[start]
            );
        }
        match self.source[index] {
            '\n' | '\r' => format_lexical_error(line + 1, 0, None, after),
            _ => format_lexical_error(line, column + 1, None, after),
        }
    }

    /// A comment is a chain of MORE matches, which restarts after each nested comment bracket,
    /// and the end of the file right after a bracket ends the token stream.
    fn skip_comment(&mut self) -> Result<(), String> {
        let start = self.offset;
        let length = self.source.len();
        if self.starts_with(start, "\\*") {
            let end = self.source[start..].iter().position(|char| matches!(char, '\n' | '\r'));
            let Some(end) = end else { return Err(self.lexical_error(start, length, "")) };
            self.offset += end + 1;
            return Ok(());
        }
        let mut depth = 0;
        let mut chain_start = start;
        let mut offset = start;
        while offset < length {
            if self.starts_with(offset, "(*") {
                depth += 1;
                offset += 2;
                if depth > 1 {
                    chain_start = offset;
                }
            } else if self.starts_with(offset, "*)") {
                depth -= 1;
                offset += 2;
                chain_start = offset;
                if depth == 0 {
                    self.offset = offset;
                    return Ok(());
                }
            } else {
                offset += 1;
            }
        }
        self.offset = offset;
        match chain_start == length {
            true => Ok(()),
            false => Err(self.lexical_error(chain_start, offset, "")),
        }
    }

    /// A token of the DEFAULT or PRAGMA lexical state, which skip every other character.
    fn skipping_token(&mut self, patterns: &[(&str, &[Pattern])]) -> Token {
        while self.offset < self.source.len() {
            let (kind, length) = match_patterns(patterns, &self.source, self.offset);
            if length > 0 {
                let token = self.token(kind, self.offset, length);
                self.offset += length;
                let name = kinds::name(kind);
                if name.starts_with("_BM") {
                    self.mode = Mode::Spec;
                }
                if name == "BEGIN_PRAGMA" {
                    self.mode = Mode::Pragma;
                }
                return token;
            }
            self.offset += 1;
        }
        self.end_of_file()
    }

    /// The longest literal or pattern at `offset`, the earliest kind among matches of that
    /// length.
    fn spec_token(&self, offset: usize) -> (Kind, usize) {
        let pattern = match_patterns(SPEC_PATTERNS, &self.source, offset);
        let available = self.source.len() - offset;
        let mut image = String::new();
        for length in (1..=kinds::longest_literal().min(available)).rev() {
            image.clear();
            image.extend(&self.source[offset..offset + length]);
            if let Some(kind) = kinds::literal(&image) {
                let is_better = length > pattern.1 || (length == pattern.1 && kind < pattern.0);
                return if is_better { (kind, length) } else { pattern };
            }
        }
        pattern
    }

    /// The number of characters JavaCC's token manager reads at `offset` while some token
    /// could still continue.
    fn token_prefix(&self, offset: usize) -> usize {
        let mut length = 0;
        let mut image = String::new();
        while offset + length < self.source.len() {
            image.push(self.source[offset + length]);
            if !kinds::is_literal_prefix(&image) {
                break;
            }
            length += 1;
        }
        length.max(string_prefix(&self.source, offset))
    }
}

/// `SimpleCharStream.UpdateLineColumn`: the line and column of each character, with tabs
/// stopping at multiples of 8. Java counts columns in UTF-16 code units.
fn positions(source: &[char]) -> (Vec<u32>, Vec<u32>) {
    let mut lines = Vec::with_capacity(source.len());
    let mut columns = Vec::with_capacity(source.len());
    let (mut line, mut column) = (1, 0);
    let (mut is_after_cr, mut is_after_lf) = (false, false);
    for &char in source {
        for _ in 0..char.len_utf16() {
            column += 1;
            if is_after_lf {
                is_after_lf = false;
                line += 1;
                column = 1;
            } else if is_after_cr {
                is_after_cr = false;
                if char == '\n' {
                    is_after_lf = true;
                } else {
                    line += 1;
                    column = 1;
                }
            }
            match char {
                '\r' => is_after_cr = true,
                '\n' => is_after_lf = true,
                '\t' => column = tab_stop(column - 1),
                _ => {}
            }
        }
        lines.push(line);
        // A character of two code units is where its first one is.
        columns.push(match char.len_utf16() {
            1 => column,
            _ => column - 1,
        });
    }
    (lines, columns)
}

fn tab_stop(column: u32) -> u32 {
    column + 8 - column % 8
}

/// `TokenMgrError.LexicalError`: the character the lexer stopped at, or the end of the file,
/// and the characters of the token it had read.
fn format_lexical_error(line: u32, column: u32, char: Option<char>, after: &str) -> String {
    let encountered = match char {
        Some(char) => {
            let code = char.encode_utf16(&mut [0; 2])[0];
            format!("\"{}\" ({code}), ", escape(&char.to_string()))
        }
        None => "<EOF> ".to_owned(),
    };
    format!(
        "Lexical error at line {line}, column {column}.  Encountered: {encountered}after : \"{}\"",
        escape(after)
    )
}

/// JavaCC's `TokenMgrError.addEscapes`, which escapes the characters of a lexical error's
/// message and of the token a parse error follows.
pub(super) fn escape(text: &str) -> String {
    let mut escaped = String::new();
    for char in text.chars() {
        match char {
            '\u{8}' => escaped.push_str("\\b"),
            '\t' => escaped.push_str("\\t"),
            '\n' => escaped.push_str("\\n"),
            '\u{c}' => escaped.push_str("\\f"),
            '\r' => escaped.push_str("\\r"),
            '"' => escaped.push_str("\\\""),
            '\'' => escaped.push_str("\\'"),
            '\\' => escaped.push_str("\\\\"),
            '\0' => {}
            ' '..='~' => escaped.push(char),
            _ => {
                for unit in char.encode_utf16(&mut [0; 2]) {
                    escaped.push_str(&format!("\\u{unit:04x}"));
                }
            }
        }
    }
    escaped
}

/// The longest match among `patterns` at `offset`, the earliest kind among matches of that
/// length, or a length of 0.
fn match_patterns(
    patterns: &[(&str, &[Pattern])],
    source: &[char],
    offset: usize,
) -> (Kind, usize) {
    let mut best: (Kind, usize) = (Kind::MAX, 0);
    for (name, alternatives) in patterns {
        let kind = kind(name);
        let length = alternatives.iter().map(|pattern| pattern(source, offset)).max().unwrap_or(0);
        if length > best.1 || (length == best.1 && kind < best.0) {
            best = (kind, length);
        }
    }
    best
}

const SPEC_PATTERNS: &[(&str, &[Pattern])] = &[
    ("_BM0", &[begin_module]),
    ("SEPARATOR", &[|source, at| repeated(source, at, '-')]),
    ("END_MODULE", &[|source, at| repeated(source, at, '=')]),
    ("NUMBER_LITERAL", &[number_literal]),
    ("STRING_LITERAL", &[string_literal]),
    ("BAND", &[|source, at| junction(source, at, "./\\")]),
    ("BOR", &[|source, at| junction(source, at, ".\\/")]),
    ("IDENTIFIER", &[identifier]),
    ("ProofStepLexeme", &[proof_step]),
    ("ProofImplicitStepLexeme", &[proof_implicit_step]),
    ("ProofStepDotLexeme", &[proof_step_dot]),
    ("BareLevelLexeme", &[|source, at| step(source, at).unwrap_or(0)]),
    ("UnnumberedStepLexeme", &[unnumbered_step]),
];

const DEFAULT_PATTERNS: &[(&str, &[Pattern])] =
    &[("BEGIN_PRAGMA", &[|source, at| literal(source, at, "--->")]), ("_BM1", &[begin_module])];

const PRAGMA_PATTERNS: &[(&str, &[Pattern])] = &[
    ("NUMBER", &[|source, at| run(source, at, |char| char.is_ascii_digit())]),
    ("_BM2", &[begin_module]),
    ("BAND", &[|source, at| junction(source, at, "./\\")]),
    ("BOR", &[|source, at| junction(source, at, ".\\/")]),
    ("IDENTIFIER", &[identifier]),
];

fn is_word(char: char) -> bool {
    char.is_ascii_alphanumeric() || char == '_'
}

/// The number of characters from `at` that `test` holds of.
fn run(source: &[char], at: usize, test: impl Fn(char) -> bool) -> usize {
    source.get(at..).map_or(0, |rest| rest.iter().take_while(|&&char| test(char)).count())
}

fn literal(source: &[char], at: usize, text: &str) -> usize {
    let length = text.chars().count();
    let matches =
        source.get(at..at + length).is_some_and(|slice| slice.iter().copied().eq(text.chars()));
    if matches { length } else { 0 }
}

/// `----+`, or `====+`.
fn repeated(source: &[char], at: usize, char: char) -> usize {
    match run(source, at, |found| found == char) {
        length if length >= 4 => length,
        _ => 0,
    }
}

/// `----+ *MODULE`.
fn begin_module(source: &[char], at: usize) -> usize {
    let dashes = repeated(source, at, '-');
    if dashes == 0 {
        return 0;
    }
    let spaces = run(source, at + dashes, |char| char == ' ');
    match literal(source, at + dashes + spaces, "MODULE") {
        0 => 0,
        module => dashes + spaces + module,
    }
}

/// `[0-9]+|\\[oO][0-7]+|\\[bB][01]+|\\[hH][0-9a-fA-F]+`.
fn number_literal(source: &[char], at: usize) -> usize {
    let digits = run(source, at, |char| char.is_ascii_digit());
    if digits > 0 || source.get(at) != Some(&'\\') {
        return digits;
    }
    let is_digit: fn(char) -> bool = match source.get(at + 1) {
        Some('o' | 'O') => |char| ('0'..='7').contains(&char),
        Some('b' | 'B') => |char| char == '0' || char == '1',
        Some('h' | 'H') => |char| char.is_ascii_hexdigit(),
        _ => return 0,
    };
    match run(source, at + 2, is_digit) {
        0 => 0,
        digits => digits + 2,
    }
}

/// The characters of a string literal from its opening quote, as far as a string literal could
/// continue: `"(?:[^"\n\r\\]|\\[ntrf\\"])*`.
fn string_body(source: &[char], at: usize) -> Option<usize> {
    if source.get(at) != Some(&'"') {
        return None;
    }
    let mut index = at + 1;
    loop {
        match source.get(index) {
            Some('"' | '\n' | '\r') | None => break,
            Some('\\') => match source.get(index + 1) {
                Some('n' | 't' | 'r' | 'f' | '\\' | '"') => index += 2,
                _ => break,
            },
            Some(_) => index += 1,
        }
    }
    Some(index - at)
}

fn string_literal(source: &[char], at: usize) -> usize {
    match string_body(source, at) {
        Some(length) if source.get(at + length) == Some(&'"') => length + 1,
        _ => 0,
    }
}

/// The characters of a string literal that a string literal could still continue, with a
/// backslash that could start an escape.
fn string_prefix(source: &[char], at: usize) -> usize {
    match string_body(source, at) {
        Some(length) => length + usize::from(source.get(at + length) == Some(&'\\')),
        None => 0,
    }
}

/// An identifier-like word followed by `/\` or `\/` right after a `.`, as in `a./\`: one of
/// `[0-9][A-Za-z0-9]*`, `[WS][a-zA-EG-Z0-9][A-Za-z0-9]*`, or `[a-zA-RT-VX-Z][A-Za-z0-9]*`.
fn junction(source: &[char], at: usize, junction: &str) -> usize {
    let Some(&first) = source.get(at) else { return 0 };
    let head = match first {
        '0'..='9' => 1,
        'W' | 'S' => match source.get(at + 1) {
            Some(&second) if second.is_ascii_alphanumeric() && second != 'F' => 2,
            _ => return 0,
        },
        _ if first.is_ascii_alphabetic() => 1,
        _ => return 0,
    };
    let word = head + run(source, at + head, |char| char.is_ascii_alphanumeric());
    match literal(source, at + word, junction) {
        0 => 0,
        length => word + length,
    }
}

/// `_\w*[A-Za-z]\w*`, `[0-9]\w*[A-Za-z]\w*`, `[WS](?:[a-zA-EG-Z_0-9]\w*)?`,
/// `[WS]F(?:[A-Za-z0-9]\w*)?`, `[a-zA-RT-VX-Z]\w*`, or `@`, `ℕ`, `ℤ`, or `ℝ`.
fn identifier(source: &[char], at: usize) -> usize {
    let Some(&first) = source.get(at) else { return 0 };
    let word = run(source, at, is_word);
    let has_letter =
        |from: usize| source[at + from..at + word].iter().any(char::is_ascii_alphabetic);
    match first {
        '_' | '0'..='9' => match has_letter(1) {
            true => word,
            false => 0,
        },
        'W' | 'S' => match source.get(at + 1) {
            Some('F') => match source.get(at + 2) {
                Some(char) if char.is_ascii_alphanumeric() => word,
                _ => 2,
            },
            Some(&char) if is_word(char) => word,
            _ => 1,
        },
        _ if first.is_ascii_alphabetic() => word,
        '@' | 'ℕ' | 'ℤ' | 'ℝ' => 1,
        _ => 0,
    }
}

/// `<(?:[0-9]+|\+|\*)>`.
fn step(source: &[char], at: usize) -> Option<usize> {
    if source.get(at) != Some(&'<') {
        return None;
    }
    let level = match source.get(at + 1) {
        Some('+' | '*') => 1,
        _ => run(source, at + 1, |char| char.is_ascii_digit()),
    };
    (level > 0 && source.get(at + 1 + level) == Some(&'>')).then_some(level + 2)
}

/// `<[0-9]+>\w+`.
fn proof_step(source: &[char], at: usize) -> usize {
    match step(source, at) {
        Some(length) if source[at + 1].is_ascii_digit() => {
            match run(source, at + length, is_word) {
                0 => 0,
                name => length + name,
            }
        }
        _ => 0,
    }
}

/// `<[+*]>[A-Za-z0-9]+`.
fn proof_implicit_step(source: &[char], at: usize) -> usize {
    match step(source, at) {
        Some(3) if matches!(source[at + 1], '+' | '*') => {
            match run(source, at + 3, |char| char.is_ascii_alphanumeric()) {
                0 => 0,
                name => 3 + name,
            }
        }
        _ => 0,
    }
}

/// `<(?:[0-9]+|\+|\*)>\w+\.+`.
fn proof_step_dot(source: &[char], at: usize) -> usize {
    let Some(length) = step(source, at) else { return 0 };
    let name = run(source, at + length, is_word);
    let dots = run(source, at + length + name, |char| char == '.');
    match name > 0 && dots > 0 {
        true => length + name + dots,
        false => 0,
    }
}

/// `<(?:[0-9]+|\+|\*)>(?:\*\.*|-\.*|\.+)`.
fn unnumbered_step(source: &[char], at: usize) -> usize {
    let Some(length) = step(source, at) else { return 0 };
    let dots = |from: usize| run(source, from, |char| char == '.');
    match source.get(at + length) {
        Some('*' | '-') => length + 1 + dots(at + length + 1),
        Some('.') => length + dots(at + length),
        _ => 0,
    }
}
