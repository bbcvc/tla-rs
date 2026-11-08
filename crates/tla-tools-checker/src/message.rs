//! TLC's codes for the errors it raises while it evaluates a spec, and its framing of a message
//! for `-tool`, as TLC's `MP.getMessage` writes it.
//!
//! TLC words each error it raises with a code from a template, and under `-tool` it frames that
//! message with its code where it builds it. So an error nested in another message, such as
//! the cause of `Evaluating invariant Inv failed.`, carries its own frame, and so does an error
//! printed in the value of a state. tla-rs words its errors as TLC does, and finds the code by
//! the template the text matches.

/// The class of a message TLC frames under `-tool`: `NONE`, `ERROR`, `TLCBUG`, `WARNING` or
/// `STATE` in `MP`.
pub const NONE: u8 = 0;
pub const ERROR: u8 = 1;
pub const WARNING: u8 = 3;
pub const STATE: u8 = 4;

/// The message as TLC prints it under `-tool`, framed with its code and class.
pub fn framed(code: u16, class: u8, text: &str) -> String {
    format!("@!@!@STARTMSG {code}:{class} @!@!@\n{text}\n@!@!@ENDMSG {code} @!@!@")
}

/// The message of an error TLC raises with a code, framed as TLC frames it when it builds it
/// under `-tool`, or the text itself for an error TLC raises without one.
pub fn nested(text: &str) -> String {
    match code_of(text) {
        Some(code) => framed(code, NONE, text),
        None => text.to_owned(),
    }
}

/// TLC's code for the error with this text, by the template of `MP` it matches.
pub fn code_of(text: &str) -> Option<u16> {
    TEMPLATES.iter().find(|(_, template)| matches(template, text)).map(|&(code, _)| code)
}

/// Whether `text` is `template` with each `%` replaced by some text, as TLC fills in the
/// parameters of a message.
fn matches(template: &str, text: &str) -> bool {
    let parts: Vec<&str> = template.split('%').collect();
    let (first, last) = (parts[0], parts[parts.len() - 1]);
    if parts.len() == 1 {
        return text == template;
    }
    let Some(mut rest) = text.strip_prefix(first) else { return false };
    for part in &parts[1..parts.len() - 1] {
        match rest.find(part) {
            Some(at) => rest = &rest[at + part.len()..],
            None => return false,
        }
    }
    rest.ends_with(last)
}

/// A template that starts with the line of the configuration file, as `MP` appends
/// `CONFIG_FILE_ERROR`.
macro_rules! config_line {
    ($rest:literal) => {
        concat!("TLC found an error in the configuration file at line %\n", $rest)
    };
}

/// The templates of the errors TLC raises with a code as it reads the configuration and
/// evaluates a spec, from `MP.getMessage0`, with `%` for each parameter. A template that
/// another one specializes comes first.
const TEMPLATES: &[(u16, &str)] = &[
    (5003, config_line!("The keyword % was not followed by an identifier.")),
    (5004, config_line!("The keyword % appeared twice.")),
    (5005, config_line!("Expected an identifier after %.")),
    (5006, config_line!("It was expecting %, but did not find it.")),
    (5002, config_line!("")),
    (5007, "TLC found an error in the configuration file:\n%"),
    (5001, "TLC encountered the following error when trying to read the configuration file %:\n%"),
    (2106, "State is not completely specified by the initial predicate:\n%"),
    (2109, "Successor state is not completely specified by %"),
    (
        2148,
        "The action formula A appearing in a WF_v(A) or SF_v(A) operator does not specify the primed value of the variable % occurring in the state formula v.\n",
    ),
    (2146, "The invariant % is not a state predicate (one with no primes or temporal operators).%"),
    (2132, "The first argument of Assert evaluated to FALSE; the second argument was:\n%"),
    (
        2154,
        "Attempted to apply the operator overridden by the Java method\n%,\nbut it produced the following error:\n%",
    ),
    (2155, "Attempted to compare % with the value\n%"),
    (2157, "Attempted to apply TransitiveClosure to a set containing\nthe following value:\n%"),
    (2158, "Attempted to check if the value:\n%\nis an element of %."),
    (2165, "Choose can only deal with numbers up to %"),
    (2266, "The % argument of % should be an %, but instead it is:\n%"),
    (2169, "The % argument of % should be a %, but instead it is:\n%"),
    (2283, "The argument of % should be a %, but instead it is:\n%"),
    (2176, "Applying % to the following value,\nwhich is not %:\n%"),
    (2177, "Attempted to apply BagUnion to the following set, whose\nelement is not a bag:\n%"),
    (2178, "Overflow when computing %"),
    (2179, "The second argument of \\div is 0."),
    (2180, "0^0 is undefined."),
    (2181, "Attempted to compute cardinality of the value\n%"),
    (2182, "Evaluating an expression of the form % when s is not a %:\n%"),
    (
        2183,
        "The % argument of % must be in the domain of its % argument:\n%\n, but instead it is\n%",
    ),
    (2184, "Attempted to apply % to the empty sequence."),
    (2145, "TLCGet(%) was undefined."),
    (2215, "TLC expected a % value, but did not find one. %"),
    (2247, "In computing %, TLC expected a % expression,\nbut instead found %.\n%"),
    (2248, "In computing %, TLC expected a % expression,\nbut didn't find one.\n%"),
    (2260, "In computing ENABLED, TLC encountered a temporal formula (%).\n%"),
    (2261, "TLC encountered a temporal formula (%) when evaluating a predicate or action.\n%"),
    (2265, "TLC can't handle a number this big.\n%"),
    (2244, "TLC can't handle real numbers.\n%"),
    (2280, "In evaluation, the identifier % is either undefined or not an operator.\n%"),
    (2222, "The constant parameter % is not assigned a value by the configuration file."),
    (
        2223,
        "In the configuration file, the identifier % appears\non the right-hand side of a <- after already appearing on the\nleft-hand side of one.",
    ),
    (2224, "The configuration file substitutes for % with the undefined identifier %."),
    (2225, "The configuration file substitutes for % with % of different number of arguments."),
    (2226, "In the configuration file, the identifier % does not appear in the specification."),
    (2227, "The configuration file cannot specify both INIT/NEXT and SPECIFICATION fields."),
    (2228, "TLC requires % not to take any argument%"),
    (2229, "The % % specified in the configuration file\nis not defined in the specification."),
    (2230, "The % of % is equal to %"),
    (2231, "The configuration file did not specify the initial state predicate."),
    (2232, "The configuration file did not specify the next state predicate."),
    (2233, "The % % cannot be a constant."),
    (2234, "The operator % cannot take any argument."),
    (2235, "The operator % is not defined in the spec."),
    (2237, "The spec is trivially false because % is false."),
    (2238, "TLC cannot handle subscript %"),
    (2239, "TLC cannot handle this conjunct of the spec:\n%"),
    (
        2240,
        "The specification contains more than one conjunct of the form [][Next]_v,\nbut TLC can handle only specifications with one next-state relation.",
    ),
    (2241, "The property % is not correctly defined."),
    (2242, "The arity of the operator % is inconsistent in the configuration file."),
    (2243, "The configuration file did not specify types for state variables."),
    (
        2273,
        "The formula % at % is an action-level formula (i.e., it contains no temporal operators). Only temporal-level (or state-level) formulas are allowed under PROPERTY or PROPERTIES. To check that action % holds in *every* step of the behavior, define a temporal property by applying%",
    ),
    (
        2274,
        "The formula % at % is an action-level formula (i.e., it contains no temporal operators). Only temporal-level (or state-level) formulas are allowed under PROPERTY or PROPERTIES. To check that infinitely many %",
    ),
    (
        2272,
        "The formula % at % is an action-level formula (i.e., it contains no temporal operators).%",
    ),
    (2281, "The configuration file substitutes constant % with non-constant %"),
    (2213, "TLC cannot handle the temporal formula %"),
    (2214, "Temporal formulas containing actions must be of forms <>[]A or []<>A."),
    (2250, "A state predicate was evaluated to a non-boolean value."),
    (2251, "Can not evaluate a temporal formula %F."),
    (2252, "Encountered an action predicate that's not a boolean."),
    (2253, "Temporal formula is a tautology (its negation is unsatisfiable)."),
    (
        2282,
        "The specification contains one or more behaviors with 65536 or more states,\nbut TLC can only handle behaviors of length up to 65535 states. The last\nstate in the behavior is:\n%",
    ),
    (
        2301,
        "TLC does not support temporal existential, nor universal, quantification over state variables.",
    ),
    (2172, "Too many possible next states for the last state in the trace."),
    (2404, "Postcondition % at % is false."),
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finds_the_code_of_an_error_by_its_template() {
        assert_eq!(code_of("The second argument of \\div is 0."), Some(2179));
        let expected = "TLC expected a boolean value, but did not find one. line 6, col 8";
        assert_eq!(code_of(expected), Some(2215));
        let argument = "The first argument of Len should be a sequence, but instead it is:\n3";
        assert_eq!(code_of(argument), Some(2169));
        let an = "The second argument of Append should be an integer, but instead it is:\n3";
        assert_eq!(code_of(an), Some(2266));
        assert_eq!(code_of("Some message TLC raises without a code."), None);
    }

    #[test]
    fn frames_an_error_raised_with_a_code() {
        assert_eq!(
            nested("The second argument of \\div is 0."),
            "@!@!@STARTMSG 2179:0 @!@!@\nThe second argument of \\div is 0.\n@!@!@ENDMSG 2179 @!@!@"
        );
        assert_eq!(nested("Uncoded."), "Uncoded.");
    }
}
