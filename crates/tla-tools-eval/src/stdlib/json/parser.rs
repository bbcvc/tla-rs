//! A strict JSON parser, as `JSON.parse` is, that keeps each number's text and each object's
//! members in order, so the conversion to values can read them as TLC does.

/// A parsed JSON value, with each number's text and each object's members in order.
pub(super) enum Json {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<Json>),
    Object(Vec<(String, Json)>),
}

/// Parses a JSON text.
pub(super) fn parse(text: &str) -> Result<Json, String> {
    Parser { source: text, text: text.as_bytes(), position: 0 }.document()
}

/// A strict JSON parser, as `JSON.parse` is.
struct Parser<'a> {
    source: &'a str,
    text: &'a [u8],
    position: usize,
}

impl Parser<'_> {
    fn error<T>(&self, expected: &str) -> Result<T, String> {
        Err(match self.text.get(self.position) {
            Some(&byte) => format!(
                "Unexpected character '{}' at position {} where {expected} should be",
                byte as char, self.position
            ),
            None => format!("Unexpected end of JSON input where {expected} should be"),
        })
    }

    fn skip_whitespace(&mut self) {
        while matches!(self.text.get(self.position), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.position += 1;
        }
    }

    fn eat(&mut self, byte: u8) -> bool {
        self.skip_whitespace();
        let is_next = self.text.get(self.position) == Some(&byte);
        self.position += usize::from(is_next);
        is_next
    }

    fn document(&mut self) -> Result<Json, String> {
        let value = self.value()?;
        self.skip_whitespace();
        if self.position < self.text.len() {
            return self.error("the end of the input");
        }
        Ok(value)
    }

    fn value(&mut self) -> Result<Json, String> {
        self.skip_whitespace();
        let rest = &self.text[self.position..];
        for (word, json) in
            [("true", Json::Bool(true)), ("false", Json::Bool(false)), ("null", Json::Null)]
        {
            if rest.starts_with(word.as_bytes()) {
                self.position += word.len();
                return Ok(json);
            }
        }
        match rest.first() {
            Some(b'"') => Ok(Json::String(self.string()?)),
            Some(b'[') => {
                self.position += 1;
                let mut items = Vec::new();
                if !self.eat(b']') {
                    loop {
                        items.push(self.value()?);
                        if self.eat(b']') {
                            break;
                        }
                        if !self.eat(b',') {
                            return self.error("',' or ']'");
                        }
                    }
                }
                Ok(Json::Array(items))
            }
            Some(b'{') => {
                self.position += 1;
                let mut members = Vec::new();
                if !self.eat(b'}') {
                    loop {
                        self.skip_whitespace();
                        if self.text.get(self.position) != Some(&b'"') {
                            return self.error("a string");
                        }
                        let key = self.string()?;
                        if !self.eat(b':') {
                            return self.error("':'");
                        }
                        members.push((key, self.value()?));
                        if self.eat(b'}') {
                            break;
                        }
                        if !self.eat(b',') {
                            return self.error("',' or '}'");
                        }
                    }
                }
                Ok(Json::Object(members))
            }
            Some(b'-' | b'0'..=b'9') => self.number(),
            _ => self.error("a value"),
        }
    }

    fn digits(&mut self) -> usize {
        let start = self.position;
        while self.text.get(self.position).is_some_and(u8::is_ascii_digit) {
            self.position += 1;
        }
        self.position - start
    }

    fn number(&mut self) -> Result<Json, String> {
        let start = self.position;
        self.position += usize::from(self.text[self.position] == b'-');
        let whole_start = self.position;
        if self.digits() == 0 || (self.text[whole_start] == b'0' && self.position - whole_start > 1)
        {
            self.position = whole_start;
            return self.error("a number");
        }
        if self.text.get(self.position) == Some(&b'.') {
            self.position += 1;
            if self.digits() == 0 {
                return self.error("a digit");
            }
        }
        if matches!(self.text.get(self.position), Some(b'e' | b'E')) {
            self.position += 1;
            if matches!(self.text.get(self.position), Some(b'+' | b'-')) {
                self.position += 1;
            }
            if self.digits() == 0 {
                return self.error("a digit");
            }
        }
        Ok(Json::Number(self.source[start..self.position].to_owned()))
    }

    fn hex4(&mut self) -> Result<u16, String> {
        let digits = self.text.get(self.position..self.position + 4);
        let unit = digits
            .and_then(|digits| std::str::from_utf8(digits).ok())
            .and_then(|digits| u16::from_str_radix(digits, 16).ok());
        match unit {
            Some(unit) => {
                self.position += 4;
                Ok(unit)
            }
            None => self.error("four hexadecimal digits"),
        }
    }

    fn string(&mut self) -> Result<String, String> {
        self.position += 1;
        let mut units: Vec<u16> = Vec::new();
        loop {
            let Some(&byte) = self.text.get(self.position) else {
                return self.error("'\"'");
            };
            match byte {
                b'"' => {
                    self.position += 1;
                    return Ok(String::from_utf16_lossy(&units));
                }
                b'\\' => {
                    self.position += 1;
                    let escaped = match self.text.get(self.position) {
                        Some(b'"') => '"',
                        Some(b'\\') => '\\',
                        Some(b'/') => '/',
                        Some(b'b') => '\u{8}',
                        Some(b'f') => '\u{c}',
                        Some(b'n') => '\n',
                        Some(b'r') => '\r',
                        Some(b't') => '\t',
                        Some(b'u') => {
                            self.position += 1;
                            units.push(self.hex4()?);
                            continue;
                        }
                        _ => return self.error("an escape"),
                    };
                    self.position += 1;
                    units.push(escaped as u16);
                }
                0..=0x1f => return self.error("a character"),
                _ => {
                    let char = self.source[self.position..].chars().next().expect("not at the end");
                    let mut buffer = [0u16; 2];
                    units.extend_from_slice(char.encode_utf16(&mut buffer));
                    self.position += char.len_utf8();
                }
            }
        }
    }
}
