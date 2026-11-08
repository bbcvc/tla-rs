//! TLC's messages as it prints them: with a prefix for the level of each, or under `-tool`
//! framed with its code and level, and its dates, durations, numbers, and estimate of a
//! fingerprint collision.

use std::time::Duration;

use chrono::{DateTime, Local};
use tla_tools_checker::message;

/// The level of a message, which TLC prints as a prefix, or under `-tool` as its class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Level {
    None,
    Error,
    Warning,
    State,
}

impl Level {
    fn class(self) -> u8 {
        match self {
            Level::None => message::NONE,
            Level::Error => message::ERROR,
            Level::Warning => message::WARNING,
            Level::State => message::STATE,
        }
    }
}

/// TLC's codes of the messages tla-rs prints, from `EC`.
pub mod ec {
    pub const GENERAL: u16 = 1000;
    pub const TLC_INITIAL_STATE: u16 = 2102;
    pub const TLC_NESTED_EXPRESSION: u16 = 2103;
    pub const TLC_ASSUMPTION_FALSE: u16 = 2104;
    pub const TLC_ASSUMPTION_EVALUATION_ERROR: u16 = 2105;
    pub const TLC_INVARIANT_VIOLATED_INITIAL: u16 = 2107;
    pub const TLC_PROPERTY_VIOLATED_INITIAL: u16 = 2108;
    pub const TLC_INVARIANT_VIOLATED_BEHAVIOR: u16 = 2110;
    pub const TLC_INVARIANT_EVALUATION_FAILED: u16 = 2111;
    pub const TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR: u16 = 2112;
    pub const TLC_ACTION_PROPERTY_EVALUATION_FAILED: u16 = 2113;
    pub const TLC_DEADLOCK_REACHED: u16 = 2114;
    pub const TLC_TEMPORAL_PROPERTY_VIOLATED: u16 = 2116;
    pub const TLC_BEHAVIOR_UP_TO_THIS_POINT: u16 = 2121;
    pub const TLC_BACK_TO_STATE: u16 = 2122;
    pub const TLC_STARTING: u16 = 2185;
    pub const TLC_FINISHED: u16 = 2186;
    pub const TLC_MODE_MC: u16 = 2187;
    pub const TLC_COMPUTING_INIT: u16 = 2189;
    pub const TLC_INIT_GENERATED1: u16 = 2190;
    pub const TLC_INIT_GENERATED2: u16 = 2191;
    pub const TLC_CHECKING_TEMPORAL_PROPS: u16 = 2192;
    pub const TLC_SUCCESS: u16 = 2193;
    pub const TLC_SEARCH_DEPTH: u16 = 2194;
    pub const TLC_STATS: u16 = 2199;
    pub const TLC_PROGRESS_STATS: u16 = 2200;
    pub const TLC_LIVE_IMPLIED: u16 = 2212;
    pub const TLC_STATE_PRINT2: u16 = 2217;
    pub const TLC_STATE_PRINT3: u16 = 2218;
    pub const TLC_SANY_END: u16 = 2219;
    pub const TLC_SANY_START: u16 = 2220;
    pub const TLC_VERSION: u16 = 2262;
    pub const TLC_COUNTER_EXAMPLE: u16 = 2264;
    pub const TLC_CHECKING_TEMPORAL_PROPS_END: u16 = 2267;
    pub const TLC_STATE_GRAPH_OUTDEGREE: u16 = 2268;
    pub const TLC_POSTCONDITION_EVALUATION_ERROR: u16 = 2405;
    pub const TLC_PARSING_FAILED: u16 = 3002;
    pub const CFG_ERROR_READING_FILE: u16 = 5001;
}

/// Prints TLC's messages to standard output.
pub struct Printer {
    warnings: bool,
    /// Whether TLC runs with `-tool`, which frames each message with its code and level.
    tool: bool,
    /// Whether a warning was printed, after the first of which TLC stops adding the hint.
    has_warned: bool,
}

impl Printer {
    pub fn new(warnings: bool, tool: bool) -> Self {
        Self { warnings, tool, has_warned: false }
    }

    pub fn is_tool(&self) -> bool {
        self.tool
    }

    /// Prints the message with TLC's `code` for it.
    pub fn print(&mut self, code: u16, level: Level, text: &str) {
        if let Some(message) = self.format(code, level, text) {
            println!("{message}");
        }
    }

    /// The message TLC prints, or `None` for a warning `-nowarning` turns off.
    fn format(&mut self, code: u16, level: Level, text: &str) -> Option<String> {
        if level == Level::Warning && !self.warnings {
            return None;
        }
        if self.tool {
            return Some(message::framed(code, level.class(), text));
        }
        let prefix = match level {
            Level::None => "",
            Level::Error => "Error: ",
            Level::Warning => "Warning: ",
            Level::State => "State ",
        };
        let mut hint = "";
        if level == Level::Warning {
            if !self.has_warned {
                hint = "\n(Use the -nowarning option to disable this warning.)";
            }
            self.has_warned = true;
        }
        Some(format!("{prefix}{text}{hint}"))
    }

    /// An error TLC raised with a code, as TLC words it when it builds it: framed with its
    /// code under `-tool`, since TLC frames it then, also inside another message.
    pub fn nested(&self, text: &str) -> String {
        match self.tool {
            true => message::nested(text),
            false => text.to_owned(),
        }
    }
}

/// TLC's date: `2024-01-31 12:34:56`, in local time.
pub fn date(time: DateTime<Local>) -> String {
    time.format("%Y-%m-%d %H:%M:%S").to_string()
}

pub fn now() -> String {
    date(Local::now())
}

/// TLC's duration for a person to read: `05s`, `01min 05s`, `01h 05min`, or `2d 01h`.
pub fn duration(duration: Duration) -> String {
    let milliseconds = duration.as_millis();
    let seconds = milliseconds / 1000 % 60;
    let minutes = milliseconds / 60_000 % 60;
    let hours = milliseconds / 3_600_000;
    if milliseconds > 86_400_000 {
        format!("{}d {:02}h", hours / 24, hours % 24)
    } else if milliseconds > 3_600_000 {
        format!("{:02}h {minutes:02}min", hours % 24)
    } else if milliseconds > 60_000 {
        format!("{minutes:02}min {seconds:02}s")
    } else {
        format!("{seconds:02}s")
    }
}

/// A count as TLC's `MP.format` prints it, with a comma between groups of three digits.
pub fn grouped(count: u64) -> String {
    let digits = count.to_string();
    let mut text = String::new();
    for (index, digit) in digits.chars().enumerate() {
        if index > 0 && (digits.len() - index) % 3 == 0 {
            text.push(',');
        }
        text.push(digit);
    }
    text
}

/// TLC's optimistic estimate of the probability of a fingerprint collision.
pub fn optimistic_probability(distinct: u64, generated: u64) -> f64 {
    distinct as f64 * ((generated.saturating_sub(distinct)) as f64 / 2f64.powi(64))
}

/// Java's `Double.toString`, which prints a number below 1E-3 or from 1E7 up in scientific
/// notation.
fn java_double(value: f64) -> String {
    let with_point = |text: String| if text.contains('.') { text } else { format!("{text}.0") };
    let magnitude = value.abs();
    if (1e-3..1e7).contains(&magnitude) {
        return with_point(format!("{value}"));
    }
    let text = format!("{value:e}");
    let (mantissa, exponent) = text.split_once('e').unwrap_or((&text, "0"));
    format!("{}E{exponent}", with_point(mantissa.to_owned()))
}

/// TLC's `ProbabilityToString`, which keeps two significant digits and drops a leading zero.
pub fn probability(value: f64) -> String {
    if value == 0.0 {
        return "0.0".into();
    }
    let text: Vec<char> = java_double(value).chars().collect();
    let digit = |index: usize| text.get(index).is_some_and(char::is_ascii_digit);
    let mut next = 0;
    let mut digits = 0;
    let mut result = String::new();
    while text.get(next) == Some(&'0') {
        next += 1;
    }
    while digit(next) {
        result.push(text[next]);
        next += 1;
        digits += 1;
    }
    if next == text.len() {
        return result;
    }
    if text[next] != '.' {
        return text.iter().collect();
    }
    next += 1;
    if digits >= 2 {
        while digit(next) {
            next += 1;
        }
    } else {
        result.push('.');
        if digits == 0 {
            while text.get(next) == Some(&'0') {
                result.push('0');
                next += 1;
            }
        }
        while digit(next) && digits < 2 {
            result.push(text[next]);
            next += 1;
            digits += 1;
        }
        if digit(next) && text[next] >= '5' {
            result = round_up(&result);
        }
        while digit(next) {
            next += 1;
        }
    }
    if next >= text.len() {
        return result;
    }
    if text[next] == 'E' {
        return format!("{result}{}", text[next..].iter().collect::<String>());
    }
    text.iter().collect()
}

/// Adds one to the last digit, carrying over nines and the decimal point.
fn round_up(digits: &str) -> String {
    let Some(last) = digits.chars().last() else { return "1".into() };
    let front = &digits[..digits.len() - 1];
    match last {
        '.' => format!("{}.", round_up(front)),
        '9' => format!("{}0", round_up(front)),
        digit => format!("{front}{}", (digit as u8 + 1) as char),
    }
}

/// TLC's summary of the outdegree of a complete state graph, from how many expanded states had
/// each number of new successors.
pub fn out_degree(buckets: &[u64]) -> Option<String> {
    let observations: u64 = buckets.iter().sum();
    if observations == 0 {
        return None;
    }
    let degrees: Vec<usize> = (0..buckets.len()).filter(|&degree| buckets[degree] > 0).collect();
    let total: u64 = buckets.iter().enumerate().map(|(degree, count)| degree as u64 * count).sum();
    let position = (observations as f64 * 0.95).floor() as u64;
    let mut cumulative = 0;
    let percentile = degrees.iter().find(|&&degree| {
        cumulative += buckets[degree];
        cumulative > position
    })?;
    let average = (total as f64 / observations as f64).round();
    Some(format!(
        "The average outdegree of the complete state graph is {average} (minimum is {}, the maximum {} and the 95th percentile is {percentile}).",
        degrees[0],
        degrees[degrees.len() - 1],
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats_durations_as_tlc_does() {
        assert_eq!(duration(Duration::from_millis(5_400)), "05s");
        assert_eq!(duration(Duration::from_secs(65)), "01min 05s");
        assert_eq!(duration(Duration::from_secs(3_900)), "01h 05min");
        assert_eq!(duration(Duration::from_secs(90_000)), "1d 01h");
    }

    #[test]
    fn formats_probabilities_as_tlc_does() {
        assert_eq!(probability(optimistic_probability(12, 18)), "3.9E-18");
        assert_eq!(probability(0.0), "0.0");
        assert_eq!(probability(0.0123), ".012");
        assert_eq!(probability(0.5), ".5");
    }

    #[test]
    fn summarizes_the_outdegree() {
        let mut buckets = vec![0; 32];
        buckets[0] = 1;
        buckets[1] = 10;
        buckets[2] = 1;
        assert_eq!(
            out_degree(&buckets).unwrap(),
            "The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 2 \
             and the 95th percentile is 2)."
        );
    }

    #[test]
    fn adds_the_hint_to_the_first_warning_only() {
        let mut printer = Printer::new(true, false);
        let first = printer.format(0, Level::Warning, "a").unwrap();
        assert!(first.ends_with("(Use the -nowarning option to disable this warning.)"));
        assert_eq!(printer.format(0, Level::Warning, "b").unwrap(), "Warning: b");
        assert_eq!(Printer::new(false, false).format(0, Level::Warning, "a"), None);
    }

    #[test]
    fn frames_a_message_with_its_code_and_level_under_tool() {
        let mut printer = Printer::new(true, true);
        assert_eq!(
            printer.format(2110, Level::Error, "Invariant Inv is violated.").unwrap(),
            "@!@!@STARTMSG 2110:1 @!@!@\nInvariant Inv is violated.\n@!@!@ENDMSG 2110 @!@!@"
        );
        assert_eq!(
            printer.format(2000, Level::Warning, "w").unwrap(),
            "@!@!@STARTMSG 2000:3 @!@!@\nw\n@!@!@ENDMSG 2000 @!@!@"
        );
    }

    #[test]
    fn groups_digits_as_tlc_does() {
        assert_eq!(grouped(0), "0");
        assert_eq!(grouped(999), "999");
        assert_eq!(grouped(3011), "3,011");
        assert_eq!(grouped(1234567), "1,234,567");
    }
}
