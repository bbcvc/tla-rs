//! TLC, ported from tla-ts `tlc/tlc-operators.ts`.

mod fingerprint;
mod pretty;
mod print;
mod random;
mod registers;

use std::time::{SystemTime, UNIX_EPOCH};

use tla_value::{LazySet, Value};

use super::{
    Outcome, arg, check_enumerable, enumerable_elements, function_pairs, java_error, op_arg,
    sequence_elements, sorted_set,
};
use crate::{Arg, Ctx, Native};
pub(crate) use fingerprint::tlc_fingerprint;
pub(crate) use pretty::pretty_print;
pub(crate) use print::strict_text;
pub(crate) use random::{JavaRandom, random_subset};

/// A method of `tlc2.module.TLC` that takes values, as `java.lang.reflect.Method` prints it.
macro_rules! tlc_method {
    ($name:literal, 1) => {
        concat!(
            "public static tlc2.value.impl.Value tlc2.module.TLC.",
            $name,
            "(tlc2.value.impl.Value)"
        )
    };
    ($name:literal, 2) => {
        concat!(
            "public static tlc2.value.impl.Value tlc2.module.TLC.",
            $name,
            "(tlc2.value.impl.Value,tlc2.value.impl.Value)"
        )
    };
}

/// The parameters of a Java method that TLC hands unevaluated arguments.
macro_rules! evaluating_method {
    ($class:literal, $name:literal) => {
        concat!(
            "public static tlc2.value.impl.Value tlc2.module.",
            $class,
            ".",
            $name,
            "(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,",
            "tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel)"
        )
    };
}

pub(super) fn lookup(name: &str) -> Option<Native> {
    Some(match name {
        "Print" => java!(print, tlc_method!("Print", 2)),
        "PrintT" => java!(print_t, tlc_method!("PrintT", 1)),
        "Assert" => java!(assert, tlc_method!("Assert", 2)),
        "JavaTime" => native!(java_time),
        "TLCGet" => tlc_get(),
        "TLCSet" => native!(registers::tlc_set),
        ":>" => java!(make_function, tlc_method!("MakeFcn", 2)),
        "@@" => java!(combine_functions, tlc_method!("CombineFcn", 2)),
        "Permutations" => java!(permutations, tlc_method!("Permutations", 1)),
        "SortSeq" => java!(sort_seq, tlc_method!("SortSeq", 2)),
        "RandomElement" => java!(random_element, tlc_method!("RandomElement", 1)),
        "Any" => native!(|_: &mut Ctx<'_>, _: &[Arg]| -> Outcome { Ok(Value::lazy(LazySet::Any)) }),
        "ToString" => java!(to_string, tlc_method!("ToString", 1)),
        "TLCEval" => java!(tlc_eval, evaluating_method!("TLCEval", "tlcEval")),
        _ => return None,
    })
}

/// `TLCGet`, which TLC evaluates with its argument in `TLCGetSet.TLCGetEval`, so it reports
/// every failure as a failure of that method.
fn tlc_get() -> Native {
    fn native(ctx: &mut Ctx<'_>, args: &[Arg]) -> tla_value::Result<Value> {
        registers::tlc_get(ctx, args).map_err(|failure| {
            java_error(evaluating_method!("TLCGetSet", "TLCGetEval"), &failure.into_error().0)
        })
    }
    native
}

/// What `Print` and `PrintT` print for a value.
fn printed(value: &Value) -> Outcome<String> {
    Ok(pretty_print(&strict_text(value)?))
}

fn print(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let (out, value) = (arg(args, 0)?, arg(args, 1)?);
    let line = format!("{}  {}", printed(out)?, printed(value)?);
    ctx.runtime().print(line);
    Ok(value.clone())
}

fn print_t(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let line = printed(arg(args, 0)?)?;
    ctx.runtime().print(line);
    Ok(Value::TRUE)
}

fn assert(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    if !matches!(arg(args, 0)?, Value::Bool(true)) {
        fail!(
            "The first argument of Assert evaluated to FALSE; the second argument was:\n{}",
            pretty_print(&arg(args, 1)?.to_string())
        );
    }
    Ok(Value::TRUE)
}

fn java_time(_: &mut Ctx<'_>, _: &[Arg]) -> Outcome {
    let seconds = SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |time| time.as_secs());
    Ok(Value::Int((seconds & 0x7fff_ffff) as i32))
}

fn make_function(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    Ok(Value::function(vec![(arg(args, 0)?.clone(), arg(args, 1)?.clone())])?)
}

/// `f @@ g`, which keeps the value of `f` for a key in both domains.
fn combine_functions(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let function = |index: usize| -> Outcome<Vec<(Value, Value)>> {
        let value = arg(args, index)?;
        if !value.is_function() {
            fail!("@@ expects a function but received {value}");
        }
        function_pairs(&value.materialize()?)
    };
    let mut pairs = function(0)?;
    pairs.extend(function(1)?);
    Ok(Value::function(pairs)?)
}

/// Every ordering of `elements`, each element first in turn.
fn orderings(elements: &[Value]) -> Vec<Vec<Value>> {
    if elements.is_empty() {
        return vec![Vec::new()];
    }
    let mut result = Vec::new();
    for (index, element) in elements.iter().enumerate() {
        let mut rest = elements.to_vec();
        rest.remove(index);
        for mut ordering in orderings(&rest) {
            ordering.insert(0, element.clone());
            result.push(ordering);
        }
    }
    result
}

fn permutations(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let elements = enumerable_elements(arg(args, 0)?, "Permutations", false)?;
    let functions = orderings(&elements)
        .into_iter()
        .map(|ordering| Value::function(elements.iter().cloned().zip(ordering).collect()))
        .collect::<tla_value::Result<Vec<_>>>()?;
    sorted_set(functions)
}

/// `SortSeq(s, Op)`: inserts each element before the first one it precedes.
fn sort_seq(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let precedes = op_arg(args, 1)?;
    let sequence = arg(args, 0)?;
    let Some(items) = sequence_elements(sequence)? else {
        fail!("SortSeq expects a sequence but received {sequence}");
    };
    let mut sorted: Vec<Value> = Vec::with_capacity(items.len());
    for item in items.iter() {
        let mut position = sorted.len();
        for (index, existing) in sorted.iter().enumerate() {
            if matches!(ctx.call(precedes, &[item.clone(), existing.clone()])?, Value::Bool(true)) {
                position = index;
                break;
            }
        }
        sorted.insert(position, item.clone());
    }
    Ok(Value::tuple(sorted))
}

fn random_element(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let set = arg(args, 0)?;
    check_enumerable(set, "RandomElement", true)?;
    Ok(ctx.runtime().with_random(|random| random::random_element(set, random))??)
}

fn to_string(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    Ok(Value::str(&strict_text(arg(args, 0)?)?))
}

/// `TLCEval(v)`, for which TLC sorts every set in `v`. A set this crate couldn't sort when it
/// built it fails to sort now.
fn tlc_eval(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    fn normalize(value: &Value) -> tla_value::Result<()> {
        match value {
            Value::Set(elements) | Value::Tuple(elements) => {
                elements.iter().try_for_each(normalize)
            }
            Value::MixedSet(_) => value.elements()?.iter().try_for_each(normalize),
            Value::Func(func) => func.values.iter().try_for_each(normalize),
            _ => Ok(()),
        }
    }
    let value = arg(args, 0)?;
    normalize(value)?;
    Ok(value.clone())
}

#[cfg(test)]
mod tests {
    use tla_value::{Result, Symbol, Value};

    use crate::stdlib::testing::{
        call, call_in, error, evaluator, int, ints, operator, string, tuple,
    };
    use crate::{Arg, Evaluator};

    fn printed(name: &str, args: &[Value]) -> (Result<Value>, Vec<String>) {
        let evaluator: Evaluator = evaluator();
        let args = args.iter().cloned().map(Arg::Value).collect();
        let result = call_in(&evaluator, "TLC", name, false, args);
        let output = evaluator.runtime().output.lock().unwrap().clone();
        (result, output)
    }

    #[test]
    fn prints_like_tlc() {
        let (result, output) = printed("Print", &[string("Test 1 OK"), Value::TRUE]);
        assert_eq!(result.unwrap().as_bool(), Some(true));
        assert_eq!(output, ["\"Test 1 OK\"  TRUE"]);
        let (result, output) = printed("PrintT", &[Value::Interval(3, 1)]);
        assert_eq!(result.unwrap().as_bool(), Some(true));
        assert_eq!(output, ["{}"]);
        let subset = Value::lazy(tla_value::LazySet::Subset(Value::lazy(tla_value::LazySet::Nat)));
        let (result, output) = printed("PrintT", &[subset]);
        assert!(result.unwrap_err().0.starts_with(
            "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLC.PrintT(tlc2.value.impl.Value),\nbut it produced the following error:\n"
        ));
        assert!(output.is_empty());
        let text = call("TLC", "ToString", &[Value::lazy(tla_value::LazySet::Subset(ints(&[1])))]);
        assert_eq!(text.unwrap().to_string(), "\"{{}, {1}}\"");
    }

    #[test]
    fn asserts_like_tlc() {
        assert_eq!(call("TLC", "Assert", &[Value::TRUE, int(1)]).unwrap().as_bool(), Some(true));
        assert_eq!(
            error("TLC", "Assert", &[Value::FALSE, string("message")]),
            "The first argument of Assert evaluated to FALSE; the second argument was:\n\"message\""
        );
        assert_eq!(
            error("TLC", "Assert", &[int(1), tuple(&[1])]),
            "The first argument of Assert evaluated to FALSE; the second argument was:\n<<1>>"
        );
    }

    #[test]
    fn builds_functions() {
        let single = call("TLC", ":>", &[string("a"), int(1)]).unwrap();
        assert_eq!(single.to_string(), "[a |-> 1]");
        assert_eq!(call("TLC", ":>", &[int(1), int(5)]).unwrap().to_string(), "<<5>>");
        let left = call("TLC", ":>", &[int(2), string("b")]).unwrap();
        let combined = call("TLC", "@@", &[left, tuple(&[7, 8])]).unwrap();
        assert_eq!(combined.to_string(), "<<7, \"b\">>");
        assert_eq!(
            error("TLC", "@@", &[int(1), tuple(&[])]),
            "@@ expects a function but received 1"
        );
        let record = Value::record(vec![(Symbol::intern("x"), int(1))]);
        let merged =
            call("TLC", "@@", &[record, Value::record(vec![(Symbol::intern("x"), int(2))])]);
        assert_eq!(merged.unwrap().to_string(), "[x |-> 1]");
    }

    #[test]
    fn permutes_sets() {
        let permutations = call("TLC", "Permutations", &[ints(&[1, 2, 3])]).unwrap();
        assert_eq!(
            permutations.to_string(),
            "{<<1, 2, 3>>, <<1, 3, 2>>, <<2, 1, 3>>, <<2, 3, 1>>, <<3, 1, 2>>, <<3, 2, 1>>}"
        );
        assert_eq!(
            call("TLC", "Permutations", &[Value::empty_set()]).unwrap().to_string(),
            "{<<>>}"
        );
        assert_eq!(
            error("TLC", "Permutations", &[Value::lazy(tla_value::LazySet::Nat)]),
            "Permutations cannot enumerate the non-enumerable set Nat"
        );
    }

    #[test]
    fn sorts_sequences_with_an_operator() {
        let less = operator(|args| Ok(Value::Bool(args[0].as_int() < args[1].as_int())));
        let args = vec![Arg::Value(tuple(&[3, 1, 2, 1])), less];
        let sorted = call_in(&evaluator(), "TLC", "SortSeq", false, args).unwrap();
        assert_eq!(sorted.to_string(), "<<1, 1, 2, 3>>");
        let args = vec![Arg::Value(int(3)), operator(|_| Ok(Value::TRUE))];
        assert_eq!(
            call_in(&evaluator(), "TLC", "SortSeq", false, args).unwrap_err().0,
            "SortSeq expects a sequence but received 3"
        );
    }

    #[test]
    fn evaluates_any_and_tlc_eval() {
        let any = call("TLC", "Any", &[]).unwrap();
        assert!(any.contains(&string("a")).unwrap());
        assert_eq!(
            call("TLC", "ToString", &[Value::tuple(vec![any])]).unwrap().to_string(),
            "\"<<ANY>>\""
        );
        assert_eq!(call("TLC", "TLCEval", &[tuple(&[1])]).unwrap().to_string(), "<<1>>");
        let mixed = Value::set(vec![int(1), string("a")]).unwrap();
        assert!(call("TLC", "TLCEval", &[mixed]).is_err());
    }
}
