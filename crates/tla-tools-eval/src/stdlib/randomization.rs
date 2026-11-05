//! Randomization, ported from tla-ts `randomization.ts`. Its choices come from TLC's random
//! generators, which [`crate::Runtime`] keeps.

use tla_tools_value::{Error, Value};

use super::tlc::random_subset;
use super::{Failure, Outcome, arg, argument_error, java_error, sorted_set};
use crate::{Arg, Ctx, Native};

pub(super) fn lookup(name: &str) -> Option<Native> {
    Some(match name {
        "RandomSubset" => native!(random_subset_of),
        "RandomSetOfSubsets" => native!(random_set_of_subsets),
        "TestRandomSetOfSubsets" => native!(test_random_set_of_subsets),
        _ => return None,
    })
}

const RANDOM_SUBSET: &str = "public static tlc2.value.impl.Value tlc2.module.Randomization.RandomSubset(tlc2.value.impl.Value,tlc2.value.impl.Value)";

fn random_subset_of(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let count = match arg(args, 0)? {
        Value::Int(count) => *count,
        count => return Err(argument_error("first", "RandomSubset", "nonnegative integer", count)),
    };
    if count < 0 {
        return Err(Failure::Eval(java_error(RANDOM_SUBSET, &count.to_string())));
    }
    let set = arg(args, 1)?;
    if !set.is_set() || (!set.is_empty()? && !set.is_enumerable()) {
        return Err(argument_error("second", "RandomSubset", "a finite set", set));
    }
    let elements = ctx.runtime().with_random(|random| random_subset(count, set, random))??;
    sorted_set(elements)
}

const SET_OF_SUBSETS: &str = "RandomSetOfSubsets";

fn count(value: &Value, position: &str) -> Outcome<i32> {
    match value {
        Value::Int(count) if *count >= 0 => Ok(*count),
        _ => Err(argument_error(position, SET_OF_SUBSETS, "nonnegative integer", value)),
    }
}

/// `RandomSetOfSubsets(k, n, S)`: `k` picks of SubsetValue's CoinTossingSubsetEnumerator, each
/// keeping every element of `S` with probability `n / Cardinality(S)`.
fn random_set_of_subsets(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let picks = count(arg(args, 0)?, "first")?;
    let size = count(arg(args, 1)?, "second")?;
    let set = arg(args, 2)?;
    if !set.is_set() || !set.is_enumerable() {
        return Err(argument_error("third", SET_OF_SUBSETS, "finite set", set));
    }
    let elements = set.elements()?;
    if elements.len() < 31 && i64::from(picks) > 1 << elements.len() {
        let expected = format!(
            "nonnegative integer that is smaller than the subset's size of 2^{}",
            elements.len()
        );
        return Err(argument_error("first", SET_OF_SUBSETS, &expected, &Value::Int(picks)));
    }
    if elements.len() < size as usize {
        let expected = "nonnegative integer in range 0..Cardinality(S)";
        return Err(argument_error("second", SET_OF_SUBSETS, expected, &Value::Int(size)));
    }
    let probability =
        if elements.is_empty() { 0.0 } else { f64::from(size) / elements.len() as f64 };
    let subsets = ctx.runtime().with_random(|random| {
        (0..picks)
            .map(|_| {
                let kept = elements.iter().filter(|_| random.next_double() < probability);
                Value::Set(kept.cloned().collect())
            })
            .collect::<Vec<_>>()
    })?;
    sorted_set(subsets)
}

fn test_random_set_of_subsets(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let mut sizes = Vec::with_capacity(5);
    for _ in 0..5 {
        let subsets = random_set_of_subsets(ctx, args)?;
        let size =
            i32::try_from(subsets.elements()?.len()).map_err(|error| Error(error.to_string()))?;
        sizes.push(Value::Int(size));
    }
    Ok(Value::tuple(sizes))
}

#[cfg(test)]
mod tests {
    use tla_tools_value::{LazySet, Result, Value};

    use crate::{Arg, Evaluator};

    use crate::stdlib::testing::{call_in, evaluator, int, ints, string};

    fn call_with(evaluator: &Evaluator, name: &str, args: &[Value]) -> Result<Value> {
        let args = args.iter().cloned().map(Arg::Value).collect();
        call_in(evaluator, "Randomization", name, false, args)
    }

    fn call(name: &str, args: &[Value]) -> Result<Value> {
        call_with(&evaluator(), name, args)
    }

    #[test]
    fn chooses_like_tla_ts() {
        let evaluator = evaluator();
        evaluator.runtime().set_seed(1);
        let call =
            |name: &str, args: &[Value]| call_with(&evaluator, name, args).unwrap().to_string();
        assert_eq!(call("RandomSubset", &[int(3), Value::Interval(1, 10)]), "{3, 8, 10}");
        let set = ints(&[1, 2, 3, 4]);
        assert_eq!(
            call("RandomSetOfSubsets", &[int(3), int(2), set.clone()]),
            "{{1, 2}, {1, 3, 4}}"
        );
        assert_eq!(call("TestRandomSetOfSubsets", &[int(3), int(2), set]), "<<2, 3, 3, 2, 3>>");
        assert_eq!(call("RandomSubset", &[int(2), Value::empty_set()]), "{}");
    }

    #[test]
    fn fails_like_tla_ts() {
        let error = |name: &str, args: &[Value]| call(name, args).unwrap_err().0;
        assert_eq!(
            error("RandomSubset", &[int(-1), ints(&[1])]),
            "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.Randomization.RandomSubset(tlc2.value.impl.Value,tlc2.value.impl.Value),\nbut it produced the following error:\n-1"
        );
        assert_eq!(
            error("RandomSubset", &[string("a"), ints(&[1])]),
            "The first argument of RandomSubset should be a nonnegative integer, but instead it is:\n\"a\""
        );
        assert_eq!(
            error("RandomSubset", &[int(1), Value::lazy(LazySet::Nat)]),
            "The second argument of RandomSubset should be a a finite set, but instead it is:\nNat"
        );
        let set = ints(&[1, 2, 3, 4]);
        assert_eq!(
            error("RandomSetOfSubsets", &[int(17), int(1), set.clone()]),
            "The first argument of RandomSetOfSubsets should be a nonnegative integer that is smaller than the subset's size of 2^4, but instead it is:\n17"
        );
        assert_eq!(
            error("RandomSetOfSubsets", &[int(1), int(5), set]),
            "The second argument of RandomSetOfSubsets should be a nonnegative integer in range 0..Cardinality(S), but instead it is:\n5"
        );
        assert_eq!(
            error("RandomSetOfSubsets", &[int(1), int(1), int(3)]),
            "The third argument of RandomSetOfSubsets should be a finite set, but instead it is:\n3"
        );
    }
}
