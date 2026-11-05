//! Sequences, ported from tla-ts `standard-modules.ts`. `Len`, `\o`, `Tail`, and `SubSeq` also
//! take strings, as TLC's Java methods do.

use std::sync::Arc;

use tla_tools_value::{LazySet, Value};

use super::{Outcome, arg, argument_error, op_arg, sequence_elements};
use crate::{Arg, Ctx, Native};

pub(super) fn lookup(name: &str) -> Option<Native> {
    Some(match name {
        "Seq" => java!(seq, SEQ),
        "Len" => java!(len, LEN),
        "\\o" => java!(concat, CONCAT),
        "Append" => java!(append, APPEND),
        "Head" => java!(head, HEAD),
        "Tail" => java!(tail, TAIL),
        "SubSeq" => java!(sub_seq, SUB_SEQ),
        "SelectSeq" => java!(select_seq, SELECT_SEQ),
        _ => return None,
    })
}

// The methods of tlc2.module.Sequences, as java.lang.reflect.Method prints them.
const SEQ: &str =
    "public static tlc2.value.impl.Value tlc2.module.Sequences.Seq(tlc2.value.impl.Value)";
const LEN: &str =
    "public static tlc2.value.impl.IntValue tlc2.module.Sequences.Len(tlc2.value.impl.Value)";
const CONCAT: &str = "public static tlc2.value.impl.Value tlc2.module.Sequences.Concat(tlc2.value.impl.Value,tlc2.value.impl.Value)";
const APPEND: &str = "public static tlc2.value.impl.Value tlc2.module.Sequences.Append(tlc2.value.impl.Value,tlc2.value.impl.Value)";
const HEAD: &str =
    "public static tlc2.value.impl.Value tlc2.module.Sequences.Head(tlc2.value.impl.Value)";
const TAIL: &str =
    "public static tlc2.value.impl.Value tlc2.module.Sequences.Tail(tlc2.value.impl.Value)";
const SUB_SEQ: &str = "public static tlc2.value.impl.Value tlc2.module.Sequences.SubSeq(tlc2.value.impl.Value,tlc2.value.impl.Value,tlc2.value.impl.Value)";
const SELECT_SEQ: &str = "public static tlc2.value.impl.Value tlc2.module.Sequences.SelectSeq(tlc2.value.impl.Value,tlc2.value.impl.Value)";

/// A sequence, or a string where TLC's method takes one, as UTF-16 code units like Java's.
enum Sequence {
    Items(Arc<[Value]>),
    Text(Vec<u16>),
}

impl Sequence {
    fn len(&self) -> usize {
        match self {
            Self::Items(items) => items.len(),
            Self::Text(text) => text.len(),
        }
    }

    fn slice(&self, start: usize, end: usize) -> Value {
        match self {
            Self::Items(items) => Value::tuple(items[start..end].to_vec()),
            Self::Text(text) => Value::str(&String::from_utf16_lossy(&text[start..end])),
        }
    }
}

/// The elements of argument `index`, failing with `message` if it isn't a sequence.
fn sequence(args: &[Arg], index: usize, message: impl Fn() -> String) -> Outcome<Arc<[Value]>> {
    let value = arg(args, index)?;
    match sequence_elements(value)? {
        Some(items) => Ok(items),
        None => fail!("{}\n{value}", message()),
    }
}

fn sequence_or_text(args: &[Arg], index: usize, message: impl Fn() -> String) -> Outcome<Sequence> {
    match arg(args, index)? {
        Value::Str(text) => Ok(Sequence::Text(text.as_str().encode_utf16().collect())),
        _ => Ok(Sequence::Items(sequence(args, index, message)?)),
    }
}

fn not_a_sequence(position: &str, name: &str) -> String {
    format!("The {position}argument of {name} should be a sequence, but instead it is:")
}

fn not_of_kind(form: &str, kind: &str) -> String {
    format!("Evaluating an expression of the form {form} when s is not a {kind}:")
}

fn seq(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    Ok(Value::lazy(LazySet::Seq(arg(args, 0)?.clone())))
}

fn len(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let length = sequence_or_text(args, 0, || not_a_sequence("", "Len"))?.len();
    Ok(Value::Int(length as i32))
}

fn concat(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    match sequence_or_text(args, 0, || not_of_kind("s \\o t", "sequence"))? {
        Sequence::Items(left) => {
            let right = sequence(args, 1, || not_of_kind("t \\o s", "sequence"))?;
            Ok(Value::tuple(left.iter().chain(right.iter()).cloned().collect()))
        }
        Sequence::Text(_) => {
            let (Value::Str(left), right) = (arg(args, 0)?, arg(args, 1)?) else { unreachable!() };
            let Value::Str(right) = right else {
                fail!("{}\n{right}", not_of_kind("t \\o s", "string"))
            };
            Ok(Value::str(&format!("{left}{right}")))
        }
    }
}

fn append(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let items = sequence(args, 0, || not_of_kind("Append(s, v)", "sequence"))?;
    let mut items = items.to_vec();
    items.push(arg(args, 1)?.clone());
    Ok(Value::tuple(items))
}

fn head(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    match sequence(args, 0, || not_a_sequence("", "Head"))?.first() {
        Some(first) => Ok(first.clone()),
        None => fail!("Attempted to apply Head to the empty sequence."),
    }
}

fn tail(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let sequence = sequence_or_text(args, 0, || not_a_sequence("", "Tail"))?;
    if sequence.len() == 0 {
        fail!("Attempted to apply Tail to the empty sequence.");
    }
    Ok(sequence.slice(1, sequence.len()))
}

fn sub_seq(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let sequence = sequence_or_text(args, 0, || not_a_sequence("first ", "SubSeq"))?;
    let integer = |index: usize| -> Outcome<i32> {
        match arg(args, index)? {
            Value::Int(value) => Ok(*value),
            value => fail!("SubSeq expects an integer but received {value}"),
        }
    };
    let (start, end) = (integer(1)?, integer(2)?);
    if start > end {
        return Ok(sequence.slice(0, 0));
    }
    let length = sequence.len() as i64;
    let out_of_domain = if start < 1 || i64::from(start) > length {
        Some(("second", start))
    } else if i64::from(end) > length {
        Some(("third", end))
    } else {
        None
    };
    if let Some((position, value)) = out_of_domain {
        fail!(
            "The {position} argument of SubSeq must be in the domain of its first argument:\n{}\n, but instead it is\n{value}",
            arg(args, 0)?
        );
    }
    Ok(sequence.slice(start as usize - 1, end as usize))
}

fn select_seq(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let test = op_arg(args, 1)?;
    let items = sequence(args, 0, || not_a_sequence("first ", "SelectSeq"))?;
    let mut selected = Vec::new();
    for item in items.iter() {
        match ctx.call(test, std::slice::from_ref(item))? {
            Value::Bool(true) => selected.push(item.clone()),
            Value::Bool(false) => {}
            result => return Err(argument_error("second", "SelectSeq", "operator", &result)),
        }
    }
    Ok(Value::tuple(selected))
}

#[cfg(test)]
mod tests {
    use tla_tools_value::{Result, Value};

    use crate::Arg;
    use crate::stdlib::testing::{call, call_in, error, evaluator, int, operator, string, tuple};

    fn java(method: &str, message: &str) -> String {
        format!(
            "Attempted to apply the operator overridden by the Java method\npublic static {method},\nbut it produced the following error:\n{message}"
        )
    }

    #[test]
    fn operates_on_sequences() {
        assert_eq!(call("Sequences", "Len", &[tuple(&[1, 2, 3])]).unwrap().as_int(), Some(3));
        let joined = call("Sequences", "\\o", &[tuple(&[1]), tuple(&[2, 3])]).unwrap();
        assert_eq!(joined.to_string(), "<<1, 2, 3>>");
        let appended = call("Sequences", "Append", &[tuple(&[]), int(4)]).unwrap();
        assert_eq!(appended.to_string(), "<<4>>");
        assert_eq!(call("Sequences", "Head", &[tuple(&[7, 8])]).unwrap().as_int(), Some(7));
        assert_eq!(call("Sequences", "Tail", &[tuple(&[7, 8])]).unwrap().to_string(), "<<8>>");
        let sub = call("Sequences", "SubSeq", &[tuple(&[1, 2, 3, 4]), int(2), int(3)]).unwrap();
        assert_eq!(sub.to_string(), "<<2, 3>>");
        let empty = call("Sequences", "SubSeq", &[tuple(&[1]), int(5), int(3)]).unwrap();
        assert_eq!(empty.to_string(), "<<>>");
        let set = call("Sequences", "Seq", &[Value::Interval(1, 2)]).unwrap();
        assert!(set.contains(&tuple(&[2, 1, 2])).unwrap());
        assert!(!set.contains(&tuple(&[3])).unwrap());
    }

    #[test]
    fn treats_strings_as_sequences_where_tlc_does() {
        assert_eq!(call("Sequences", "Len", &[string("abc")]).unwrap().as_int(), Some(3));
        let joined = call("Sequences", "\\o", &[string("ab"), string("c")]).unwrap();
        assert_eq!(joined.to_string(), "\"abc\"");
        assert_eq!(call("Sequences", "Tail", &[string("abc")]).unwrap().to_string(), "\"bc\"");
        let sub = call("Sequences", "SubSeq", &[string("abcd"), int(2), int(3)]).unwrap();
        assert_eq!(sub.to_string(), "\"bc\"");
        assert_eq!(
            error("Sequences", "\\o", &[string("ab"), tuple(&[1])]),
            "Evaluating an expression of the form t \\o s when s is not a string:\n<<1>>"
        );
        assert_eq!(
            error("Sequences", "Head", &[string("ab")]),
            "The argument of Head should be a sequence, but instead it is:\n\"ab\""
        );
    }

    #[test]
    fn fails_like_tlc() {
        assert_eq!(
            error("Sequences", "Head", &[tuple(&[])]),
            "Attempted to apply Head to the empty sequence."
        );
        assert_eq!(
            error("Sequences", "Tail", &[string("")]),
            "Attempted to apply Tail to the empty sequence."
        );
        assert_eq!(
            error("Sequences", "Len", &[int(1)]),
            "The argument of Len should be a sequence, but instead it is:\n1"
        );
        assert_eq!(
            error("Sequences", "Append", &[int(1), int(2)]),
            "Evaluating an expression of the form Append(s, v) when s is not a sequence:\n1"
        );
        assert_eq!(
            error("Sequences", "SubSeq", &[tuple(&[1, 2]), int(0), int(1)]),
            "The second argument of SubSeq must be in the domain of its first argument:\n<<1, 2>>\n, but instead it is\n0"
        );
        assert_eq!(
            error("Sequences", "SubSeq", &[tuple(&[1, 2]), int(1), int(3)]),
            "The third argument of SubSeq must be in the domain of its first argument:\n<<1, 2>>\n, but instead it is\n3"
        );
        assert_eq!(
            error("Sequences", "SubSeq", &[tuple(&[1, 2]), string("a"), int(3)]),
            "SubSeq expects an integer but received \"a\""
        );
    }

    fn select(test: fn(&[Value]) -> Result<Value>, items: &[i32]) -> Result<Value> {
        let args = vec![Arg::Value(tuple(items)), operator(test)];
        call_in(&evaluator(), "Sequences", "SelectSeq", false, args)
    }

    #[test]
    fn selects_with_an_operator() {
        let even = |args: &[Value]| Ok(Value::Bool(args[0].as_int().unwrap() % 2 == 0));
        assert_eq!(select(even, &[1, 2, 3, 4]).unwrap().to_string(), "<<2, 4>>");
        assert_eq!(
            select(|_| Ok(Value::Int(1)), &[1]).unwrap_err().0,
            "The second argument of SelectSeq should be a operator, but instead it is:\n1"
        );
        let failing = |args: &[Value]| args[0].equals(&Value::str("a")).map(Value::Bool);
        assert_eq!(
            select(failing, &[1]).unwrap_err().0,
            java(
                "tlc2.value.impl.Value tlc2.module.Sequences.SelectSeq(tlc2.value.impl.Value,tlc2.value.impl.Value)",
                "Attempted to check equality of integer 1 with non-integer:\n\"a\""
            )
        );
    }
}
