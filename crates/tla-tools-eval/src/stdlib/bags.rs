//! Bags, ported from tla-ts `bags.ts`. A bag is a function from its elements to their positive
//! counts. TLC overrides every operator of Bags but `SubBag`, which tla-ts implements natively
//! with the same result as its TLA+ definition.

use tla_tools_resolve::{DefBody, ExprKind};
use tla_tools_value::{Error, Value};

use super::{
    Failure, Outcome, arg, argument_error, function_pairs, java_class, java_error, op_arg,
    sorted_set,
};
use crate::native::OperatorKind;
use crate::{Arg, Ctx, Native};

pub(super) fn lookup(name: &str, uses_integers: bool) -> Option<Native> {
    Some(match name {
        "EmptyBag" => native!(|_: &mut Ctx<'_>, _: &[Arg]| -> Outcome { Ok(Value::empty_tuple()) }),
        "IsABag" => native!(is_a_bag),
        "BagCardinality" => native!(bag_cardinality),
        "BagIn" => native!(bag_in),
        "CopiesIn" => native!(copies_in),
        "\\oplus" => native!(bag_cup),
        "\\ominus" => native!(bag_diff),
        "BagUnion" => native!(bag_union),
        "\\sqsubseteq" => native!(sq_subseteq),
        "BagOfAll" => native!(bag_of_all),
        "SubBag" if uses_integers => native!(sub_bag::<true>),
        "SubBag" => native!(sub_bag::<false>),
        "BagToSet" => native!(bag_to_set),
        "SetToBag" => native!(set_to_bag),
        _ => return None,
    })
}

/// A method of `tlc2.module.Bags` as `java.lang.reflect.Method` prints it.
macro_rules! bags_method {
    ($result:literal, $name:literal, 1) => {
        concat!("public static ", $result, " tlc2.module.Bags.", $name, "(tlc2.value.impl.Value)")
    };
    ($result:literal, $name:literal, 2) => {
        concat!(
            "public static ",
            $result,
            " tlc2.module.Bags.",
            $name,
            "(tlc2.value.impl.Value,tlc2.value.impl.Value)"
        )
    };
}

const BAG_DIFF: &str = bags_method!("tlc2.value.impl.Value", "BagDiff", 2);
const SQ_SUBSETEQ: &str = bags_method!("tlc2.value.IBoolValue", "SqSubseteq", 2);
const BAG_UNION: &str = bags_method!("tlc2.value.impl.Value", "BagUnion", 1);
const BAG_OF_ALL: &str = bags_method!("tlc2.value.impl.Value", "BagOfAll", 2);
const BAG_CUP: &str = bags_method!("tlc2.value.impl.Value", "BagCup", 2);
const BAG_CARDINALITY: &str = bags_method!("tlc2.value.impl.IntValue", "BagCardinality", 1);

type Pairs = Vec<(Value, Value)>;

fn not_a(name: &str, expected: &str, value: &Value) -> Failure {
    Failure::Module(Error(format!(
        "Applying {name} to the following value,\nwhich is not {expected}:\n{value}"
    )))
}

/// The pairs of a function, enumerated if TLC doesn't enumerate it yet, or `None` for another
/// value.
fn to_function(value: &Value) -> Outcome<Option<Pairs>> {
    if !value.is_function() {
        return Ok(None);
    }
    Ok(Some(function_pairs(&value.materialize()?)?))
}

fn function(args: &[Arg], index: usize, name: &str) -> Outcome<Pairs> {
    let value = arg(args, index)?;
    to_function(value)?.ok_or_else(|| not_a(name, "a function with a finite domain", value))
}

fn position(index: usize) -> &'static str {
    if index == 0 { "first" } else { "second" }
}

fn bag(args: &[Arg], index: usize, name: &str) -> Outcome<Pairs> {
    let value = arg(args, index)?;
    to_function(value)?.ok_or_else(|| argument_error(position(index), name, "bag", value))
}

fn finite_elements(
    set: &Value,
    failure: impl FnOnce() -> Failure,
) -> Outcome<std::sync::Arc<[Value]>> {
    if !set.is_set() || !set.is_enumerable() {
        return Err(failure());
    }
    Ok(set.elements()?)
}

fn is_bag(pairs: &Pairs) -> bool {
    pairs.iter().all(|(_, count)| matches!(count, Value::Int(count) if *count > 0))
}

fn find_count<'a>(pairs: &'a Pairs, element: &Value) -> Outcome<Option<&'a Value>> {
    for (key, count) in pairs {
        if key.equals(element)? {
            return Ok(Some(count));
        }
    }
    Ok(None)
}

/// Bags.java casts each count to `IntValue`, so a count that isn't an integer fails with Java's
/// `ClassCastException`.
fn to_count(value: &Value, method: &str) -> Outcome<i32> {
    match value {
        Value::Int(count) => Ok(*count),
        _ => {
            let class = format!("tlc2.value.impl.{}", java_class(value));
            Err(Failure::Eval(java_error(
                method,
                &format!(
                    "class {class} cannot be cast to class tlc2.value.impl.IntValue ({class} and tlc2.value.impl.IntValue are in unnamed module of loader 'app')"
                ),
            )))
        }
    }
}

fn add_counts(left: &Value, right: &Value, method: &str) -> Outcome<Value> {
    let sum = i64::from(to_count(left, method)?) + i64::from(to_count(right, method)?);
    match i32::try_from(sum) {
        Ok(sum) => Ok(Value::Int(sum)),
        Err(_) => fail!("Overflow when computing {left}+{right}"),
    }
}

/// The count of the element at `index` of `pairs` less its count in `other`, wrapping as Java
/// ints do.
fn subtract_counts(pairs: &Pairs, index: usize, other: &Pairs, method: &str) -> Outcome<i32> {
    let removed = find_count(other, &pairs[index].0)?;
    let count = to_count(&pairs[index].1, method)?;
    match removed {
        None => Ok(count),
        Some(removed) => Ok(count.wrapping_sub(to_count(removed, method)?)),
    }
}

fn merge_bags(bags: Vec<Pairs>, method: &str) -> Outcome {
    let mut merged: Pairs = Vec::new();
    for bag in bags {
        for (key, count) in bag {
            let mut existing = None;
            for (index, (known, _)) in merged.iter().enumerate() {
                if known.equals(&key)? {
                    existing = Some(index);
                    break;
                }
            }
            match existing {
                Some(index) => merged[index].1 = add_counts(&merged[index].1, &count, method)?,
                None => merged.push((key, count)),
            }
        }
    }
    Ok(Value::function(merged)?)
}

fn is_a_bag(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    Ok(Value::Bool(to_function(arg(args, 0)?)?.is_some_and(|pairs| is_bag(&pairs))))
}

fn bag_cardinality(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let value = arg(args, 0)?;
    let mut total = Value::Int(0);
    for (_, count) in function(args, 0, "BagCardinality")? {
        if !matches!(count, Value::Int(count) if count > 0) {
            return Err(not_a("BagCardinality", "a bag", value));
        }
        total = add_counts(&total, &count, BAG_CARDINALITY)?;
    }
    Ok(total)
}

/// The count of argument 0 in the bag of argument 1, or `None` if it isn't in the bag.
fn copies(args: &[Arg], name: &str) -> Outcome<Option<i32>> {
    let pairs = function(args, 1, name)?;
    match find_count(&pairs, arg(args, 0)?)? {
        None => Ok(None),
        Some(Value::Int(count)) => Ok(Some(*count)),
        Some(_) => Err(argument_error("second", name, "bag", arg(args, 1)?)),
    }
}

fn bag_in(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    Ok(Value::Bool(copies(args, "BagIn")?.is_some_and(|count| count > 0)))
}

fn copies_in(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    Ok(Value::Int(copies(args, "CopiesIn")?.unwrap_or(0)))
}

fn bag_cup(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let mut bags = Vec::with_capacity(2);
    for index in 0..2 {
        let pairs = bag(args, index, "(+)")?;
        if !is_bag(&pairs) {
            return Err(argument_error(position(index), "(+)", "bag", arg(args, index)?));
        }
        bags.push(pairs);
    }
    merge_bags(bags, BAG_CUP)
}

fn bag_diff(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let left = bag(args, 0, "(-)")?;
    let right = bag(args, 1, "(-)")?;
    let mut pairs = Vec::new();
    for index in 0..left.len() {
        let count = subtract_counts(&left, index, &right, BAG_DIFF)?;
        if count > 0 {
            pairs.push((left[index].0.clone(), Value::Int(count)));
        }
    }
    Ok(Value::function(pairs)?)
}

fn bag_union(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let set = arg(args, 0)?;
    let elements = finite_elements(set, || not_a("BagUnion", "a finite enumerable set", set))?;
    if elements.len() < 2 {
        return Ok(elements.first().cloned().unwrap_or_else(Value::empty_tuple));
    }
    let mut bags = Vec::with_capacity(elements.len());
    for element in elements.iter() {
        match to_function(element)? {
            Some(pairs) => bags.push(pairs),
            None => fail!(
                "Attempted to apply BagUnion to the following set, whose\nelement is not a bag:\n{set}"
            ),
        }
    }
    merge_bags(bags, BAG_UNION)
}

fn sq_subseteq(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let left = function(args, 0, "\\sqsubseteq")?;
    let right = function(args, 1, "\\sqsubseteq")?;
    for index in 0..left.len() {
        if subtract_counts(&left, index, &right, SQ_SUBSETEQ)? > 0 {
            return Ok(Value::FALSE);
        }
    }
    Ok(Value::TRUE)
}

/// The literal an operator's body is, which TLC passes to Bags.java instead of the operator.
fn literal_body(ctx: &Ctx<'_>, operator: &crate::Operator) -> Option<String> {
    let OperatorKind::Def { def, .. } = &operator.0 else { return None };
    let DefBody::Expr(body) = &ctx.evaluator.spec.def(*def).body else { return None };
    match &body.kind {
        ExprKind::Int(value) => Some(value.to_string()),
        ExprKind::Str(text) => Some(Value::Str(*text).to_string()),
        _ => None,
    }
}

fn bag_of_all(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let operator = op_arg(args, 0)?;
    if let Some(literal) = literal_body(ctx, operator) {
        fail!(
            "The first argument of BagOfAll should be an operator, but instead it is:\n{literal}"
        );
    }
    let value = arg(args, 1)?;
    let Some(pairs) = to_function(value)? else {
        return Err(argument_error("second", "BagOfAll", "function with a finite domain", value));
    };
    let mut bags = Vec::with_capacity(pairs.len());
    for (key, count) in pairs {
        bags.push(vec![(ctx.call(operator, &[key])?, count)]);
    }
    merge_bags(bags, BAG_OF_ALL)
}

/// `SubBag(B)`, which compares the counts with the `\geq` of Naturals, or of Integers when TLC
/// loads it.
fn sub_bag<const INTEGERS: bool>(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let value = arg(args, 0)?;
    if !value.is_function() {
        fail_eval!("DOMAIN expects a function but received {value}");
    }
    let function = value.materialize()?;
    let pairs = function_pairs(&function)?;
    let range = sorted_set(pairs.iter().map(|(_, count)| count.clone()).collect())?;
    let range = range.elements()?;
    if let Some(invalid) = range.iter().find(|count| !matches!(count, Value::Int(_))) {
        let name = if INTEGERS { ">=" } else { ">" };
        let (position, value) = if matches!(range[0], Value::Int(_)) {
            ("second", invalid)
        } else {
            ("first", &range[0])
        };
        fail!(
            "The {position} argument of {name} should be an integer, but instead it is:\n{value}"
        );
    }
    let mut counts = Vec::with_capacity(pairs.len());
    for (_, count) in &pairs {
        match count {
            Value::Int(count) if *count >= 1 => counts.push(*count),
            _ => fail_eval!(
                "Attempted to apply a function to {function}, which is not in its domain"
            ),
        }
    }
    let mut sub_bags: Vec<Pairs> = vec![Vec::new()];
    for ((key, _), count) in pairs.iter().zip(counts) {
        let mut extended = Vec::with_capacity(sub_bags.len() * (count as usize + 1));
        for entries in sub_bags {
            extended.push(entries.clone());
            for copies in 1..=count {
                let mut more = entries.clone();
                more.push((key.clone(), Value::Int(copies)));
                extended.push(more);
            }
        }
        sub_bags = extended;
    }
    let bags =
        sub_bags.into_iter().map(Value::function).collect::<tla_tools_value::Result<Vec<_>>>()?;
    sorted_set(bags)
}

fn bag_to_set(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let value = arg(args, 0)?;
    if !value.is_function() {
        return Err(not_a("BagToSet", "a function with a finite domain", value));
    }
    Ok(value.materialize()?.domain()?)
}

fn set_to_bag(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let set = arg(args, 0)?;
    let elements =
        finite_elements(set, || not_a("BagToSet", "a function with a finite domain", set))?;
    Ok(Value::function(elements.iter().map(|element| (element.clone(), Value::Int(1))).collect())?)
}

#[cfg(test)]
mod tests;
