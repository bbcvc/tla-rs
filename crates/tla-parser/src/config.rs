//! TLC model configuration (`.cfg`) files.
//!
//! A port of TLC's `ModelConfig.parse` by way of tla-ts `src/config.ts`. Like TLC, the parser
//! takes any token where it expects a name or a value, so `CONSTANT N = <<` assigns the model
//! value `<<`.

use tla_ast::Symbol;

/// A value TLC can read from a configuration file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConfigValue {
    Int(i64),
    /// A string, with its escape sequences kept as written, as TLC keeps them.
    Str(Symbol),
    Bool(bool),
    ModelValue(Symbol),
    Set(Vec<ConfigValue>),
}

/// `N = 3`, `F(1, 2) = 3`, or `N = [M] 3`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstantAssignment {
    pub name: Symbol,
    pub args: Vec<ConfigValue>,
    pub value: ConfigValue,
    /// The module named in `[M]`, which applies the assignment in that module.
    pub module: Option<Symbol>,
}

/// `N <- Def` or `N <- [M] Def`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstantSubstitution {
    pub name: Symbol,
    pub target: Symbol,
    pub module: Option<Symbol>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModelConfig {
    pub init: Option<Symbol>,
    pub next: Option<Symbol>,
    pub specification: Option<Symbol>,
    pub invariants: Vec<Symbol>,
    pub properties: Vec<Symbol>,
    pub constraints: Vec<Symbol>,
    pub action_constraints: Vec<Symbol>,
    pub constants: Vec<ConstantAssignment>,
    pub substitutions: Vec<ConstantSubstitution>,
    pub check_deadlock: bool,
    pub symmetry: Option<Symbol>,
    pub view: Option<Symbol>,
    pub alias: Option<Symbol>,
    pub postconditions: Vec<Symbol>,
    pub possible: Vec<Symbol>,
    pub periodic: Option<Symbol>,
    pub rl_reward: Option<Symbol>,
}

impl Default for ModelConfig {
    fn default() -> Self {
        Self {
            init: None,
            next: None,
            specification: None,
            invariants: Vec::new(),
            properties: Vec::new(),
            constraints: Vec::new(),
            action_constraints: Vec::new(),
            constants: Vec::new(),
            substitutions: Vec::new(),
            check_deadlock: true,
            symmetry: None,
            view: None,
            alias: None,
            postconditions: Vec::new(),
            possible: Vec::new(),
            periodic: None,
            rl_reward: None,
        }
    }
}

/// A configuration file TLC can't read, with TLC's wording.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("{message}")]
pub struct ConfigError {
    pub message: String,
}

impl ConfigError {
    fn syntax(line: usize, problem: &str) -> Self {
        Self {
            message: format!(
                "TLC found an error in the configuration file at line {line}\n{problem}"
            ),
        }
    }
}

const KEYWORDS: &[&str] = &[
    "CONSTANT",
    "CONSTANTS",
    "INIT",
    "NEXT",
    "SPECIFICATION",
    "INVARIANT",
    "INVARIANTS",
    "PROPERTY",
    "PROPERTIES",
    "CONSTRAINT",
    "CONSTRAINTS",
    "ACTION_CONSTRAINT",
    "ACTION_CONSTRAINTS",
    "SYMMETRY",
    "VIEW",
    "CHECK_DEADLOCK",
    "ALIAS",
    "POSTCONDITION",
    "POSTCONDITIONS",
    "_POSSIBLE",
    "_PERIODIC",
    "_RL_REWARD",
];

const SYMBOLS: &[&str] = &["<-", "<<", ">>", "=", "{", "}", ",", "[", "]", "(", ")", "!"];

/// Characters that make up TLA+ operator tokens such as `\o` or `|->`.
const OPERATOR_CHARS: &str = "\\/<>=~|&*+-.:^%@#$?!";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TokenKind {
    Word,
    Number,
    Str,
    Symbol,
    End,
}

#[derive(Clone, Debug)]
struct Token<'a> {
    kind: TokenKind,
    text: &'a str,
    line: usize,
}

impl Token<'_> {
    fn is_keyword(&self) -> bool {
        self.kind == TokenKind::Word && KEYWORDS.contains(&self.text)
    }
}

/// TLC reads a configuration with the TLA+ lexer. A lexical error ends the tokens, and TLC
/// reports it only if parsing reaches it.
fn tokenize(source: &str) -> (Vec<Token<'_>>, Option<ConfigError>) {
    let mut tokens = Vec::new();
    let mut index = 0;
    let mut line = 1;
    let bytes = source.as_bytes();
    let lexical_error = |line: usize| ConfigError {
        message: format!(
            "TLC found an error in the configuration file:\nLexical error at line {line}"
        ),
    };
    while index < source.len() {
        let rest = &source[index..];
        let char = rest.chars().next().unwrap();
        if char.is_whitespace() {
            line += usize::from(char == '\n');
            index += char.len_utf8();
            continue;
        }
        if rest.starts_with("\\*") {
            index += rest.find('\n').unwrap_or(rest.len());
            continue;
        }
        if rest.starts_with("(*") {
            let Some(end) = rest.find("*)") else {
                return (tokens, Some(lexical_error(line + rest.matches('\n').count() + 1)));
            };
            line += rest[..end].matches('\n').count();
            index += end + 2;
            continue;
        }
        let token_line = line;
        let word_length =
            rest.bytes().take_while(|byte| byte.is_ascii_alphanumeric() || *byte == b'_').count();
        let (kind, length) = if word_length > 0 {
            let is_number = rest.as_bytes()[..word_length].iter().all(u8::is_ascii_digit);
            (if is_number { TokenKind::Number } else { TokenKind::Word }, word_length)
        } else if char == '"' {
            let mut end = 1;
            let mut is_closed = false;
            while end < rest.len() {
                match bytes[index + end] {
                    b'"' => {
                        is_closed = true;
                        break;
                    }
                    b'\n' => break,
                    b'\\' if bytes.get(index + end + 1).is_some_and(|next| *next != b'\n') => {
                        end += 2
                    }
                    _ => end += 1,
                }
            }
            if !is_closed {
                return (tokens, Some(lexical_error(line)));
            }
            tokens.push(Token { kind: TokenKind::Str, text: &rest[1..end], line: token_line });
            index += end + 1;
            continue;
        } else if let Some(symbol) = SYMBOLS.iter().find(|symbol| rest.starts_with(**symbol)) {
            (TokenKind::Symbol, symbol.len())
        } else if char == '\\' && rest[1..].starts_with(|next: char| next.is_ascii_alphabetic()) {
            // A backslash operator such as `\o` or `\cup`.
            (TokenKind::Word, 1 + rest[1..].bytes().take_while(u8::is_ascii_alphabetic).count())
        } else {
            let length = rest
                .chars()
                .take_while(|char| OPERATOR_CHARS.contains(*char))
                .map(char::len_utf8)
                .sum();
            if length == 0 {
                return (tokens, Some(lexical_error(line)));
            }
            (TokenKind::Word, length)
        };
        tokens.push(Token { kind, text: &rest[..length], line: token_line });
        index += length;
    }
    tokens.push(Token { kind: TokenKind::End, text: "", line });
    (tokens, None)
}

struct ConfigParser<'a> {
    tokens: Vec<Token<'a>>,
    lexical_error: Option<ConfigError>,
    index: usize,
    config: ModelConfig,
}

type Result<T> = std::result::Result<T, ConfigError>;

impl<'a> ConfigParser<'a> {
    fn advance(&mut self) -> Result<Token<'a>> {
        if self.index >= self.tokens.len()
            && let Some(error) = self.lexical_error.take()
        {
            return Err(error);
        }
        let token = self.tokens[self.index.min(self.tokens.len() - 1)].clone();
        self.index += 1;
        Ok(token)
    }

    fn value(&mut self, token: Token<'a>) -> Result<ConfigValue> {
        match token.kind {
            TokenKind::Number => {
                return token
                    .text
                    .parse()
                    .map(ConfigValue::Int)
                    .map_err(|_| ConfigError::syntax(token.line, "The number is too large."));
            }
            TokenKind::Str => return Ok(ConfigValue::Str(Symbol::intern(token.text))),
            TokenKind::End => {
                return Err(ConfigError::syntax(
                    token.line,
                    "It was expecting a value, but did not find it.",
                ));
            }
            _ => {}
        }
        match token.text {
            "TRUE" => Ok(ConfigValue::Bool(true)),
            "FALSE" => Ok(ConfigValue::Bool(false)),
            "{" => {
                let mut elements = Vec::new();
                let mut current = self.advance()?;
                if current.text != "}" {
                    loop {
                        elements.push(self.value(current)?);
                        current = self.advance()?;
                        if current.text != "," {
                            break;
                        }
                        current = self.advance()?;
                    }
                }
                if current.text != "}" {
                    return Err(ConfigError::syntax(
                        current.line,
                        "It was expecting }, but did not find it.",
                    ));
                }
                Ok(ConfigValue::Set(elements))
            }
            text => Ok(ConfigValue::ModelValue(Symbol::intern(text))),
        }
    }

    /// The module name in `[M]` after `=` or `<-`.
    fn module_scope(&mut self, operator: &str) -> Result<Symbol> {
        let name = self.advance()?;
        if name.kind == TokenKind::End {
            return Err(ConfigError::syntax(
                name.line,
                &format!("Expected an identifier after {operator}[."),
            ));
        }
        let close = self.advance()?;
        if close.text != "]" {
            return Err(ConfigError::syntax(
                close.line,
                "It was expecting ], but did not find it.",
            ));
        }
        Ok(Symbol::intern(name.text))
    }

    /// Reads assignments until the next keyword, which it returns.
    fn constants(&mut self, keyword_line: usize) -> Result<Token<'a>> {
        loop {
            let first = self.advance()?;
            if first.kind == TokenKind::End || first.is_keyword() {
                return Ok(first);
            }
            let mut name = first.text.to_owned();
            let mut current = self.advance()?;
            while current.text == "!" {
                name = format!("{name}!{}", self.advance()?.text);
                current = self.advance()?;
            }
            let name = Symbol::intern(&name);
            if current.text == "<-" {
                current = self.advance()?;
                let module =
                    if current.text == "[" { Some(self.module_scope("<-")?) } else { None };
                if module.is_some() {
                    current = self.advance()?;
                }
                if current.kind == TokenKind::End {
                    let after = if module.is_some() { "<-[mod]" } else { "<-" };
                    return Err(ConfigError::syntax(
                        current.line,
                        &format!("Expected an identifier after {after}."),
                    ));
                }
                self.config.substitutions.push(ConstantSubstitution {
                    name,
                    target: Symbol::intern(current.text),
                    module,
                });
                continue;
            }
            let mut args = Vec::new();
            if current.text == "(" {
                loop {
                    let token = self.advance()?;
                    args.push(self.value(token)?);
                    current = self.advance()?;
                    if current.text != "," {
                        break;
                    }
                }
                if current.text != ")" {
                    return Err(ConfigError::syntax(keyword_line, ""));
                }
                current = self.advance()?;
            }
            if current.text != "=" {
                return Err(ConfigError::syntax(
                    current.line,
                    "It was expecting = or <-, but did not find it.",
                ));
            }
            current = self.advance()?;
            let module = if current.text == "[" { Some(self.module_scope("=")?) } else { None };
            if module.is_some() {
                current = self.advance()?;
            }
            let value = self.value(current)?;
            self.config.constants.push(ConstantAssignment { name, args, value, module });
        }
    }

    /// Reads names until the next keyword, which it returns.
    fn names(&mut self, list: fn(&mut ModelConfig) -> &mut Vec<Symbol>) -> Result<Token<'a>> {
        loop {
            let token = self.advance()?;
            if token.kind == TokenKind::End || token.is_keyword() {
                return Ok(token);
            }
            list(&mut self.config).push(Symbol::intern(token.text));
        }
    }

    fn parse(mut self) -> Result<ModelConfig> {
        let mut is_deadlock_set = false;
        let mut current = self.advance()?;
        while current.kind != TokenKind::End {
            let keyword = current.text;
            let line = current.line;
            if !current.is_keyword() {
                return Err(ConfigError::syntax(
                    line,
                    "It was expecting a keyword, but did not find it.",
                ));
            }
            let single: Option<fn(&mut ModelConfig) -> &mut Option<Symbol>> = match keyword {
                "INIT" => Some(|config| &mut config.init),
                "NEXT" => Some(|config| &mut config.next),
                "SPECIFICATION" => Some(|config| &mut config.specification),
                "VIEW" => Some(|config| &mut config.view),
                "SYMMETRY" => Some(|config| &mut config.symmetry),
                "ALIAS" => Some(|config| &mut config.alias),
                "_PERIODIC" => Some(|config| &mut config.periodic),
                "_RL_REWARD" => Some(|config| &mut config.rl_reward),
                _ => None,
            };
            let list: Option<fn(&mut ModelConfig) -> &mut Vec<Symbol>> = match keyword {
                "INVARIANT" | "INVARIANTS" => Some(|config| &mut config.invariants),
                "PROPERTY" | "PROPERTIES" => Some(|config| &mut config.properties),
                "CONSTRAINT" | "CONSTRAINTS" => Some(|config| &mut config.constraints),
                "ACTION_CONSTRAINT" | "ACTION_CONSTRAINTS" => {
                    Some(|config| &mut config.action_constraints)
                }
                "POSTCONDITION" | "POSTCONDITIONS" => Some(|config| &mut config.postconditions),
                "_POSSIBLE" => Some(|config| &mut config.possible),
                _ => None,
            };
            let missing_argument = || {
                ConfigError::syntax(
                    line,
                    &format!("The keyword {keyword} was not followed by an identifier."),
                )
            };
            if let Some(slot) = single {
                let argument = self.advance()?;
                if argument.kind == TokenKind::End {
                    return Err(missing_argument());
                }
                if slot(&mut self.config).replace(Symbol::intern(argument.text)).is_some() {
                    return Err(ConfigError::syntax(
                        line,
                        &format!("The keyword {keyword} appeared twice."),
                    ));
                }
                current = self.advance()?;
            } else if let Some(list) = list {
                current = self.names(list)?;
            } else if keyword == "CHECK_DEADLOCK" {
                let value = self.advance()?;
                if value.kind == TokenKind::End {
                    return Err(missing_argument());
                }
                if value.text != "TRUE" && value.text != "FALSE" {
                    return Err(ConfigError::syntax(
                        value.line,
                        "It was expecting TRUE or FALSE, but did not find it.",
                    ));
                }
                if is_deadlock_set {
                    return Err(ConfigError::syntax(
                        line,
                        &format!("The keyword {keyword} appeared twice."),
                    ));
                }
                is_deadlock_set = true;
                self.config.check_deadlock = value.text == "TRUE";
                current = self.advance()?;
            } else {
                current = self.constants(line)?;
            }
        }
        Ok(self.config)
    }
}

pub fn parse_config(source: &str) -> std::result::Result<ModelConfig, ConfigError> {
    let (tokens, lexical_error) = tokenize(source);
    ConfigParser { tokens, lexical_error, index: 0, config: ModelConfig::default() }.parse()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn symbol(text: &str) -> Symbol {
        Symbol::intern(text)
    }

    #[test]
    fn reads_keywords_and_constants() {
        let config = parse_config(
            r#"
            \* A comment
            CONSTANTS
                N = 3
                Procs = {p1, p2}
                Name = "a\"b"
                Def <- MCDef
                \o <- +
                F(1, TRUE) = [M] 2
            (* block
               comment *)
            INIT Init NEXT Next
            INVARIANTS TypeOK Safe
            PROPERTY Live
            CHECK_DEADLOCK FALSE
            "#,
        )
        .unwrap();
        assert_eq!(config.init, Some(symbol("Init")));
        assert_eq!(config.next, Some(symbol("Next")));
        assert_eq!(config.invariants, vec![symbol("TypeOK"), symbol("Safe")]);
        assert_eq!(config.properties, vec![symbol("Live")]);
        assert!(!config.check_deadlock);
        assert_eq!(config.constants.len(), 4);
        assert_eq!(config.constants[0].value, ConfigValue::Int(3));
        assert_eq!(
            config.constants[1].value,
            ConfigValue::Set(vec![
                ConfigValue::ModelValue(symbol("p1")),
                ConfigValue::ModelValue(symbol("p2"))
            ])
        );
        assert_eq!(config.constants[2].value, ConfigValue::Str(symbol("a\\\"b")));
        assert_eq!(config.constants[3].args, vec![ConfigValue::Int(1), ConfigValue::Bool(true)]);
        assert_eq!(config.constants[3].module, Some(symbol("M")));
        let substitutions: Vec<_> = config
            .substitutions
            .iter()
            .map(|substitution| (substitution.name.as_str(), substitution.target.as_str()))
            .collect();
        assert_eq!(substitutions, [("Def", "MCDef"), ("\\o", "+")]);
    }

    #[test]
    fn reports_errors_with_tlc_wording() {
        let duplicate = parse_config("INIT A\nINIT B").unwrap_err();
        assert_eq!(
            duplicate.message,
            "TLC found an error in the configuration file at line 2\nThe keyword INIT appeared twice."
        );
        let missing = parse_config("CONSTANT N 3").unwrap_err();
        assert!(missing.message.ends_with("It was expecting = or <-, but did not find it."));
        assert!(parse_config("Init").is_err());
    }

    #[test]
    fn defers_lexical_errors_until_reached() {
        assert!(parse_config("INIT Init\n\"unterminated").is_err());
        let config = parse_config("SPECIFICATION Spec").unwrap();
        assert_eq!(config.specification, Some(symbol("Spec")));
    }
}
