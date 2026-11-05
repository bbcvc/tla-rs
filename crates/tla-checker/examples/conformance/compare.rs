//! What a run of the checker reports, what TLC's record says, and how they compare.

use tla_checker::{Outcome, Status};

/// The fields of an outcome a child process reports, one per line.
#[derive(Clone, Debug, Default)]
pub struct Reported {
    pub status: String,
    pub violation: Option<String>,
    pub trace_length: Option<u64>,
    pub generated: Option<u64>,
    pub distinct: Option<u64>,
    pub depth: Option<u64>,
    pub message: Option<String>,
}

/// The text `Reported::encode` escaped.
fn unescape(text: &str) -> String {
    let mut unescaped = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(char) = chars.next() {
        unescaped.push(match (char, char == '\\') {
            (_, true) => match chars.next() {
                Some('n') => '\n',
                Some('t') => '\t',
                Some(other) => other,
                None => '\\',
            },
            (char, false) => char,
        });
    }
    unescaped
}

impl Reported {
    pub fn from_outcome(outcome: &Outcome) -> Self {
        Self {
            status: outcome.status.name().to_owned(),
            violation: outcome.violation.clone(),
            trace_length: outcome.trace_length.map(|length| length as u64),
            generated: outcome.generated,
            distinct: outcome.distinct,
            depth: outcome.depth,
            message: outcome.message.clone(),
        }
    }

    pub fn encode(&self) -> String {
        let escape =
            |text: &str| text.replace('\\', "\\\\").replace('\n', "\\n").replace('\t', "\\t");
        let number = |value: Option<u64>| value.map_or(String::new(), |value| value.to_string());
        [
            self.status.clone(),
            self.violation.as_deref().map(escape).unwrap_or_default(),
            number(self.trace_length),
            number(self.generated),
            number(self.distinct),
            number(self.depth),
            self.message.as_deref().map(escape).unwrap_or_default(),
        ]
        .join("\t")
    }

    pub fn decode(line: &str) -> Option<Self> {
        let fields: Vec<&str> = line.split('\t').collect();
        if fields.len() != 7 {
            return None;
        }
        let unescape = |text: &str| (!text.is_empty()).then(|| unescape(text));
        let number = |text: &str| text.parse().ok();
        Some(Self {
            status: fields[0].to_owned(),
            violation: unescape(fields[1]),
            trace_length: number(fields[2]),
            generated: number(fields[3]),
            distinct: number(fields[4]),
            depth: number(fields[5]),
            message: unescape(fields[6]),
        })
    }
}

/// tla-ts's record of TLC's result for a model.
pub struct Expected {
    pub status: String,
    pub violation: Option<String>,
    pub generated: Option<u64>,
    pub distinct: Option<u64>,
    pub depth: Option<u64>,
    pub trace_length: Option<u64>,
    /// How long TLC ran.
    pub milliseconds: Option<u64>,
}

/// How long TLC may run before an error it reports is the end of its resources, as tla-ts's
/// conformance runner takes it (`--max-tlc-ms`).
pub const TLC_TIME_LIMIT_MS: u64 = 20_000;

impl Expected {
    pub fn from_json(record: &serde_json::Value) -> Self {
        let number = |field: &str| record[field].as_u64();
        Self {
            status: record["status"].as_str().unwrap_or_default().to_owned(),
            violation: record["violation"].as_str().map(str::to_owned),
            generated: number("generatedStates"),
            distinct: number("distinctStates"),
            depth: number("depth"),
            trace_length: number("traceLength"),
            milliseconds: number("tlcMilliseconds"),
        }
    }

    /// Whether TLC reached a verdict. TLC errs after a long run only when it runs out of memory
    /// or disk on a state space too large for it, which tla-ts's runner leaves out.
    pub fn has_verdict(&self) -> bool {
        self.status != "error" || self.milliseconds.unwrap_or(0) <= TLC_TIME_LIMIT_MS
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Verdict {
    Match,
    Mismatch,
    Unsupported,
    /// TLC has no verdict to compare with.
    Unjudged,
    Timeout,
    Crash,
}

impl Verdict {
    pub fn name(self) -> &'static str {
        match self {
            Verdict::Match => "match",
            Verdict::Mismatch => "mismatch",
            Verdict::Unsupported => "unsupported",
            Verdict::Unjudged => "no-verdict",
            Verdict::Timeout => "timeout",
            Verdict::Crash => "crash",
        }
    }
}

/// tla-ts's `compareOutcome`: what differs, if anything.
/// With `verdicts_only`, as for a search with several workers, only the status, the violation,
/// and the distinct states are compared.
pub fn compare(
    expected: &Expected,
    actual: &Reported,
    verdicts_only: bool,
) -> (Verdict, Option<String>) {
    if actual.status == Status::Unsupported.name() {
        return (Verdict::Unsupported, actual.message.clone());
    }
    if expected.status == "error" {
        return match actual.status.as_str() {
            "error" => (Verdict::Match, None),
            status => (Verdict::Mismatch, Some(format!("expected an error, got {status}"))),
        };
    }
    // TLC exits as for a violated assumption when a postcondition fails.
    let status = match actual.status.as_str() {
        "postcondition-violation" => "assumption-violation",
        status => status,
    };
    if status != expected.status {
        let error =
            actual.message.as_deref().map(|message| format!(" ({message})")).unwrap_or_default();
        return (
            Verdict::Mismatch,
            Some(format!("expected {}, got {}{error}", expected.status, actual.status)),
        );
    }
    let mut differences = Vec::new();
    let mut compare = |field: &str, expected: Option<String>, actual: Option<String>| {
        if let Some(expected) = expected
            && Some(&expected) != actual.as_ref()
        {
            differences.push(format!(
                "{field}: expected {expected}, got {}",
                actual.unwrap_or("none".into())
            ));
        }
    };
    let text = |value: Option<u64>| value.map(|value| value.to_string());
    compare("violation", expected.violation.clone(), actual.violation.clone());
    compare("distinctStates", text(expected.distinct), text(actual.distinct));
    if !verdicts_only {
        compare("generatedStates", text(expected.generated), text(actual.generated));
        compare("depth", text(expected.depth), text(actual.depth));
        compare("traceLength", text(expected.trace_length), text(actual.trace_length));
    }
    match differences.is_empty() {
        true => (Verdict::Match, None),
        false => (Verdict::Mismatch, Some(differences.join("; "))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn reported(status: Status) -> Reported {
        Reported {
            status: status.name().to_owned(),
            violation: None,
            trace_length: None,
            generated: None,
            distinct: None,
            depth: None,
            message: None,
        }
    }

    fn expected(record: serde_json::Value) -> Expected {
        Expected::from_json(&record)
    }

    #[test]
    pub fn encodes_outcomes_in_one_line() {
        let outcome = Reported {
            violation: Some("Inv".into()),
            trace_length: Some(3),
            message: Some("a\tb\nc \\n".into()),
            ..reported(Status::InvariantViolation)
        };
        let line = outcome.encode();
        assert!(!line.contains('\n'));
        let decoded = Reported::decode(&line).unwrap();
        assert_eq!(decoded.encode(), line);
        assert_eq!(decoded.message.as_deref(), Some("a\tb\nc \\n"));
        assert!(decoded.generated.is_none());
    }

    #[test]
    fn compares_outcomes_as_tla_ts_does() {
        let success = Reported {
            generated: Some(4),
            distinct: Some(3),
            depth: Some(2),
            ..reported(Status::Success)
        };
        let record = serde_json::json!({
            "status": "success", "generatedStates": 4, "distinctStates": 3, "depth": 2
        });
        assert_eq!(compare(&expected(record), &success, false).0, Verdict::Match);
        let record = serde_json::json!({
            "status": "success", "generatedStates": 5, "distinctStates": 3, "depth": 2
        });
        assert_eq!(compare(&expected(record), &success, false).0, Verdict::Mismatch);
        // TLC exits as for a violated assumption when a postcondition fails.
        let postcondition =
            Reported { trace_length: Some(0), ..reported(Status::PostconditionViolation) };
        let record = serde_json::json!({ "status": "assumption-violation", "traceLength": 0 });
        assert_eq!(compare(&expected(record), &postcondition, false).0, Verdict::Match);
        let record = serde_json::json!({ "status": "liveness-violation", "traceLength": 2 });
        let live = Reported { trace_length: Some(2), ..reported(Status::LivenessViolation) };
        assert_eq!(compare(&expected(record.clone()), &success, false).0, Verdict::Mismatch);
        assert_eq!(compare(&expected(record), &live, false).0, Verdict::Match);
        let record = serde_json::json!({ "status": "error" });
        assert_eq!(compare(&expected(record.clone()), &success, false).0, Verdict::Mismatch);
        assert_eq!(compare(&expected(record), &reported(Status::Error), false).0, Verdict::Match);
    }

    #[test]
    fn leaves_out_tlc_running_out_of_resources() {
        let record = serde_json::json!({ "status": "error", "tlcMilliseconds": 300_022 });
        assert!(!expected(record).has_verdict());
        let record = serde_json::json!({ "status": "error", "tlcMilliseconds": 400 });
        assert!(expected(record).has_verdict());
        let record = serde_json::json!({ "status": "success", "tlcMilliseconds": 300_022 });
        assert!(expected(record).has_verdict());
    }
}
