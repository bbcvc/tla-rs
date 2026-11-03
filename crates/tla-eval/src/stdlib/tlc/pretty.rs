//! TLC's pretty printer, which breaks a printed value across lines of at most 80 columns,
//! ported from tla-ts `pretty-print.ts`, itself a port of TLC's `tlc2.pprint`. It parses the
//! printed text back, and prints the text as it is whenever that parse fails.

use std::fmt::Write;

/// The width TLC's pretty printer breaks lines at.
const WIDTH: i64 = 80;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Constant,
    Set,
    Sequence,
    Record,
    Function,
    Subset,
    Pair,
}

/// A value TLC's pretty printer parsed back from its text: `first..=last` in the text.
struct Node {
    kind: Kind,
    first: usize,
    last: usize,
    children: Vec<Node>,
}

struct Delimiters {
    open: &'static str,
    close: &'static str,
    pad: &'static str,
    separator: &'static str,
    divider: &'static str,
    divider_pad: &'static str,
}

fn delimiters(kind: Kind) -> Delimiters {
    let (open, close, pad, separator, divider, divider_pad) = match kind {
        Kind::Set => ("{ ", " }", "  ", ",", "", ""),
        Kind::Sequence => ("<< ", " >>", "   ", ",", "", ""),
        Kind::Subset => ("SUBSET ", " ", " ", ",", "", ""),
        Kind::Function => ("( ", " )", "  ", " @@", " :>", "    "),
        _ => ("[ ", " ]", "  ", ",", " |->", "    "),
    };
    Delimiters { open, close, pad, separator, divider, divider_pad }
}

/// Java's Character#isWhitespace.
fn is_whitespace(char: char) -> bool {
    matches!(
        char as u32,
        0x09..=0x0d | 0x1c..=0x20 | 0x1680 | 0x2028 | 0x2029 | 0x205f | 0x3000
    ) || (('\u{2000}'..='\u{200a}').contains(&char) && char != '\u{2007}')
}

fn is_digit(char: char) -> bool {
    char.is_numeric()
}

fn is_letter_or_digit(char: char) -> bool {
    char.is_alphabetic() || char.is_numeric()
}

/// Parses printed values back as TLC's pretty printer does, which gives up on what it doesn't
/// know.
struct Parser<'a> {
    text: &'a [char],
}

impl Parser<'_> {
    fn skip_while(&self, mut index: usize, is_match: fn(char) -> bool) -> usize {
        while index < self.text.len() && is_match(self.text[index]) {
            index += 1;
        }
        index
    }

    fn skip_whitespace(&self, index: usize) -> Option<usize> {
        let end = self.skip_while(index, is_whitespace);
        (end < self.text.len()).then_some(end)
    }

    fn starts_with(&self, prefix: &str, index: usize) -> bool {
        let mut chars = self.text.get(index..).unwrap_or_default().iter();
        prefix.chars().all(|char| chars.next() == Some(&char))
    }

    fn items(
        &self,
        kind: Kind,
        first: usize,
        start: usize,
        close: char,
        separator: &str,
        item: impl Fn(&Self, usize) -> Option<Node>,
    ) -> Option<Node> {
        let mut node = Node { kind, first, last: first, children: Vec::new() };
        let mut position = self.skip_whitespace(start);
        while let Some(index) = position {
            if self.text[index] == close {
                break;
            }
            let child = item(self, index)?;
            let after_item = self.skip_whitespace(child.last + 1)?;
            let after_separator = if self.starts_with(separator, after_item) {
                after_item + separator.chars().count()
            } else {
                after_item
            };
            node.children.push(child);
            position = self.skip_whitespace(after_separator);
        }
        node.last = position?;
        Some(node)
    }

    fn pair(&self, index: usize, divider: &str) -> Option<Node> {
        let left = self.parse(index)?;
        let divider_index = self.skip_whitespace(left.last + 1)?;
        if !self.starts_with(divider, divider_index) {
            return None;
        }
        let right = self.parse(self.skip_whitespace(divider_index + divider.chars().count())?)?;
        Some(Node { kind: Kind::Pair, first: index, last: right.last, children: vec![left, right] })
    }

    fn constant(&self, first: usize) -> Option<Node> {
        let constant = |last: usize| Node { kind: Kind::Constant, first, last, children: vec![] };
        let char = self.text[first];
        if char == '"' {
            // TLC finds the closing quote without regard for escapes.
            let closing = self.text[first + 1..].iter().position(|&char| char == '"')?;
            return Some(constant(first + 1 + closing));
        }
        if is_digit(char) {
            let low_end = self.skip_while(first, is_digit);
            if self.starts_with("..", low_end)
                && self.text.get(low_end + 2).is_some_and(|&char| is_digit(char))
            {
                return Some(constant(self.skip_while(low_end + 2, is_digit) - 1));
            }
        }
        if char == '-' {
            if first + 1 >= self.text.len() {
                return None;
            }
            return Some(constant(self.skip_while(first + 1, is_digit) - 1));
        }
        if !is_letter_or_digit(char) {
            return None;
        }
        Some(constant(self.skip_while(first, is_letter_or_digit) - 1))
    }

    fn parse(&self, index: usize) -> Option<Node> {
        let first = self.skip_whitespace(index)?;
        match self.text[first] {
            '{' => self.items(Kind::Set, first, first + 1, '}', ",", Self::parse),
            '<' => {
                let mut node =
                    self.items(Kind::Sequence, first, first + 2, '>', ",", Self::parse)?;
                if node.last + 1 >= self.text.len() {
                    return None;
                }
                node.last += 1;
                Some(node)
            }
            '[' => self.items(Kind::Record, first, first + 1, ']', ",", |parser, index| {
                parser.pair(index, "|->")
            }),
            '(' => self.items(Kind::Function, first, first + 1, ')', "@@", |parser, index| {
                parser.pair(index, ":>")
            }),
            _ if self.starts_with("SUBSET", first) => {
                let element = self.parse(self.skip_whitespace(first + 6)?)?;
                Some(Node {
                    kind: Kind::Subset,
                    first,
                    last: element.last,
                    children: vec![element],
                })
            }
            _ => self.constant(first),
        }
    }
}

/// Breaks a printed value across lines of at most 80 columns as TLC's pretty printer does, or
/// returns it as it is if TLC's printer can't parse it.
pub(crate) fn pretty_print(text: &str) -> String {
    let chars: Vec<char> = text.chars().collect();
    let parser = Parser { text: &chars };
    let tree = match parser.parse(0) {
        Some(tree) if tree.last + 1 >= chars.len() => tree,
        _ => return text.to_owned(),
    };
    let printer = Printer { text: &chars };
    printer.format(&tree, WIDTH, 0, "").unwrap_or_else(|| text.to_owned())
}

struct Printer<'a> {
    text: &'a [char],
}

impl Printer<'_> {
    fn text(&self, node: &Node) -> String {
        self.text[node.first..=node.last].iter().collect()
    }

    fn length(node: &Node) -> i64 {
        (node.last - node.first + 1) as i64
    }

    fn format(&self, node: &Node, width: i64, trailer: i64, pad: &str) -> Option<String> {
        if Self::length(node) <= width - trailer || node.kind == Kind::Constant {
            return Some(self.text(node));
        }
        if node.kind == Kind::Pair {
            return None;
        }
        let delimiters = delimiters(node.kind);
        let inner_width = width - delimiters.open.len().max(delimiters.pad.len()) as i64;
        let inner_trailer = trailer + delimiters.close.len() as i64;
        let inner_pad = format!("{pad}{}", delimiters.pad);
        let inner = if matches!(node.kind, Kind::Function | Kind::Record) {
            self.format_pairs(&node.children, inner_width, inner_trailer, &inner_pad, &delimiters)
        } else {
            self.format_items(
                &node.children,
                inner_width,
                inner_trailer,
                &inner_pad,
                delimiters.separator,
            )
        }?;
        Some(format!("{}{inner}{}", delimiters.open, delimiters.close))
    }

    fn format_items(
        &self,
        items: &[Node],
        width: i64,
        trailer: i64,
        pad: &str,
        separator: &str,
    ) -> Option<String> {
        let mut text = String::new();
        for (index, item) in items.iter().enumerate() {
            let is_last = index + 1 == items.len();
            let item_trailer = if is_last { trailer } else { separator.len() as i64 };
            text.push_str(&self.format(item, width, item_trailer, pad)?);
            if !is_last {
                write!(text, "{separator}\n{pad}").expect("writing to a string succeeds");
            }
        }
        Some(text)
    }

    fn format_pairs(
        &self,
        pairs: &[Node],
        width: i64,
        trailer: i64,
        pad: &str,
        delimiters: &Delimiters,
    ) -> Option<String> {
        let mut text = String::new();
        for (index, pair) in pairs.iter().enumerate() {
            let is_last = index + 1 == pairs.len();
            let (left, right) = (&pair.children[0], &pair.children[1]);
            let ending =
                if is_last { String::new() } else { format!("{}\n{pad}", delimiters.separator) };
            let divider_length = delimiters.divider.len() as i64;
            let separator_length = delimiters.separator.len() as i64;
            let pair_length = Self::length(left) + divider_length + 1 + Self::length(right);
            let fits = if is_last {
                pair_length <= width - trailer
            } else {
                pair_length + separator_length <= width
            };
            if fits {
                let (left, right) = (self.text(left), self.text(right));
                write!(text, "{left}{} {right}{ending}", delimiters.divider)
                    .expect("writing to a string succeeds");
                continue;
            }
            let left = if Self::length(left) + divider_length <= width {
                Some(self.text(left))
            } else {
                self.format(left, width, trailer + divider_length, pad)
            };
            let right_pad = format!("{pad}{}", delimiters.divider_pad);
            let right = self.format(
                right,
                width - delimiters.divider_pad.len() as i64,
                if is_last { trailer } else { separator_length },
                &right_pad,
            );
            let (left, right) = (left?, right?);
            write!(text, "{left}{}\n{right_pad}{right}{ending}", delimiters.divider)
                .expect("writing to a string succeeds");
        }
        Some(text)
    }
}

#[cfg(test)]
mod tests {
    use super::pretty_print;

    #[test]
    fn breaks_lines_like_tlcs_pretty_printer() {
        let rows = ["<<1, 2, 3, 4, 5, 6, 7, 8, 9, 10>>"; 10];
        let table = format!("<<{}>>", rows.join(", "));
        assert_eq!(pretty_print(&table), format!("<< {} >>", rows.join(",\n   ")));
        let records =
            (1..=5).map(|x| format!("[fielda |-> {x}, fieldb |-> 1..{x}]")).collect::<Vec<_>>();
        assert_eq!(
            pretty_print(&format!("<<{}>>", records.join(", "))),
            format!("<< {} >>", records.join(",\n   "))
        );
        let field = format!("field{}", "a".repeat(78));
        assert_eq!(
            pretty_print(&format!("[{field} |-> <<1, 2>>]")),
            format!("[ {field} |->\n      <<1, 2>> ]")
        );
        let function = (2..=9).map(|x| format!("{x} :> {}", x * 100_000_000)).collect::<Vec<_>>();
        assert_eq!(
            pretty_print(&format!("({})", function.join(" @@ "))),
            format!("( {} )", function.join(" @@\n  "))
        );
        let escaped = format!("<<\"a\\\"b\", \"{}\", \"{}\">>", "c".repeat(44), "d".repeat(30));
        assert_eq!(pretty_print(&escaped), escaped);
        assert_eq!(pretty_print("<<1, 2>>"), "<<1, 2>>");
    }

    #[test]
    fn breaks_nested_sequences() {
        let triple = |x: i32, y: i32| {
            format!(
                "<<{}>>",
                (1..=3).map(|z| format!("<<{x}, {y}, {z}>>")).collect::<Vec<_>>().join(", ")
            )
        };
        let plane = |x: i32| {
            format!("<<{}>>", (1..=3).map(|y| triple(x, y)).collect::<Vec<_>>().join(", "))
        };
        let cube = format!("<<{}>>", (1..=3).map(plane).collect::<Vec<_>>().join(", "));
        let expected = "<< << <<<<1, 1, 1>>, <<1, 1, 2>>, <<1, 1, 3>>>>,\n      <<<<1, 2, 1>>, <<1, 2, 2>>, <<1, 2, 3>>>>,\n      <<<<1, 3, 1>>, <<1, 3, 2>>, <<1, 3, 3>>>> >>,\n   << <<<<2, 1, 1>>, <<2, 1, 2>>, <<2, 1, 3>>>>,\n      <<<<2, 2, 1>>, <<2, 2, 2>>, <<2, 2, 3>>>>,\n      <<<<2, 3, 1>>, <<2, 3, 2>>, <<2, 3, 3>>>> >>,\n   << <<<<3, 1, 1>>, <<3, 1, 2>>, <<3, 1, 3>>>>,\n      <<<<3, 2, 1>>, <<3, 2, 2>>, <<3, 2, 3>>>>,\n      <<<<3, 3, 1>>, <<3, 3, 2>>, <<3, 3, 3>>>> >> >>";
        assert_eq!(pretty_print(&cube), expected);
    }
}
