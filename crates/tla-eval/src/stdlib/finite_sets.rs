//! FiniteSets, ported from tla-ts `standard-modules.ts` and the `isFiniteSet` and
//! `getCardinality` of its `values.ts`.

use tla_value::{Error, LazySet, Result, Value, bail};

use super::{Outcome, arg, is_overridden_set, kind_name};
use crate::{Arg, Ctx, Native};

pub(super) fn lookup(name: &str) -> Option<Native> {
    Some(match name {
        "IsFiniteSet" => java!(is_finite_set, IS_FINITE_SET),
        "Cardinality" => java!(cardinality_of, CARDINALITY),
        _ => return None,
    })
}

const IS_FINITE_SET: &str =
    "public static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value)";
const CARDINALITY: &str = "public static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value)";

fn is_finite_set(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    Ok(Value::Bool(is_finite(arg(args, 0)?)?))
}

fn cardinality_of(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let set = arg(args, 0)?;
    if !set.is_set() || is_overridden_set(set) {
        fail!("Attempted to compute cardinality of the value\n{set}");
    }
    Ok(Value::Int(cardinality(set)?))
}

/// Whether TLC finds a value finite. TLC takes a finite function for a finite set.
pub(super) fn is_finite(value: &Value) -> Result<bool> {
    let set = match value {
        Value::Set(_)
        | Value::MixedSet(_)
        | Value::Interval(..)
        | Value::Tuple(_)
        | Value::Func(_) => return Ok(true),
        Value::LazyFunc(_) => {
            bail!("Attempted to check if the function:\n{value}\nis a finite set.")
        }
        Value::Lazy(set) => set,
        _ => bail!("Attempted to check if the {} {value} is a finite set.", kind_name(value)),
    };
    let infinite_check = || Error(format!("Attempted to check if the set {value}is finite."));
    match &**set {
        LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => Ok(false),
        LazySet::Seq(base) => Ok(is_finite(base)? && base.is_empty()?),
        LazySet::Subset(base) => is_finite(base),
        LazySet::FuncSet { domain, range } => {
            let is_finite_domain = is_finite(domain)?;
            if is_finite_domain && domain.is_empty()? {
                return Ok(true);
            }
            let is_finite_range = is_finite(range)?;
            if is_finite_range && range.is_empty()? {
                return Ok(true);
            }
            Ok(is_finite_range && (is_finite_domain || cardinality(range)? == 1))
        }
        LazySet::RecordSet(fields) => {
            are_all_finite(&fields.iter().map(|(_, set)| set).collect::<Vec<_>>())
        }
        LazySet::Product(factors) => are_all_finite(&factors.iter().collect::<Vec<_>>()),
        LazySet::Union(base) => {
            if !base.is_set() || is_overridden_set(base) {
                bail!(
                    "Attempted to check if the nonenumerable set:\nUNION({base})\nis a finite set."
                );
            }
            for set in base.elements()?.iter() {
                if !is_finite(set)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        LazySet::Cup(left, right) => Ok(is_finite(left)? && is_finite(right)?),
        LazySet::Cap(left, right) => {
            if !is_finite(left)? && !is_finite(right)? {
                return Err(infinite_check());
            }
            Ok(true)
        }
        LazySet::Minus(left, right) => {
            if is_finite(left)? {
                return Ok(true);
            }
            if !is_finite(right)? {
                return Err(infinite_check());
            }
            Ok(false)
        }
        LazySet::Filtered { base, .. } => {
            if !is_finite(base)? {
                bail!(
                    "Attempted to check if expression of form {{x \\in S : p(x)}} is a finite set, but cannot check if S:\n{base}\nis finite."
                );
            }
            Ok(true)
        }
    }
}

/// Whether a product of sets is finite: it is if one of them is empty.
fn are_all_finite(sets: &[&Value]) -> Result<bool> {
    let mut are_all_finite = true;
    for set in sets {
        if !is_finite(set)? {
            are_all_finite = false;
        } else if set.is_empty()? {
            return Ok(true);
        }
    }
    Ok(are_all_finite)
}

fn overflow(value: &Value) -> Error {
    Error(format!("Overflow when computing the number of elements in:\n{value}"))
}

/// The number of elements TLC counts in a value: a function counts its domain.
pub(super) fn cardinality(value: &Value) -> Result<i32> {
    let set = match value {
        Value::Tuple(items) => return Ok(items.len() as i32),
        Value::Func(func) => return Ok(func.keys.len() as i32),
        Value::LazyFunc(_) => return cardinality(&value.domain()?),
        Value::Interval(low, high) => {
            let size = (i64::from(*high) - i64::from(*low) + 1).max(0);
            return i32::try_from(size).map_err(|_| {
                Error(format!(
                    "Size of interval value exceeds the maximum representable size (32bits): {low}..{high}."
                ))
            });
        }
        Value::Set(elements) => return Ok(elements.len() as i32),
        Value::MixedSet(_) => return Ok(value.elements()?.len() as i32),
        Value::Lazy(set) => set,
        Value::Model(_) => {
            bail!("Attempted to compute the number of elements in the model value {value}.")
        }
        _ => bail!(
            "Attempted to compute the number of elements in the {} {value}.",
            kind_name(value)
        ),
    };
    match &**set {
        LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any | LazySet::Seq(_) => {
            bail!("Attempted to compute the number of elements in the overridden value {value}.")
        }
        LazySet::Subset(base) => {
            let size = cardinality(base)?;
            if size >= 31 {
                return Err(overflow(value));
            }
            Ok(1 << size)
        }
        LazySet::FuncSet { domain, range } => {
            if domain.is_empty()? {
                return Ok(1);
            }
            if range.is_empty()? {
                return Ok(0);
            }
            let range_size = cardinality(range)?;
            if range_size == 1 {
                return Ok(1);
            }
            let domain_size = cardinality(domain)?;
            let mut size: i64 = 1;
            for _ in 0..domain_size {
                size *= i64::from(range_size);
                if size > i64::from(i32::MAX) {
                    return Err(overflow(value));
                }
            }
            Ok(size as i32)
        }
        LazySet::RecordSet(fields) => {
            if value.is_empty()? {
                return Ok(0);
            }
            product_size(fields.iter().map(|(_, set)| set), || overflow(value))
        }
        LazySet::Product(factors) => {
            if value.is_empty()? {
                return Ok(0);
            }
            product_size(factors.iter(), || {
                Error(format!("Overflow when computing the number of elements in {value}"))
            })
        }
        _ => Ok(value.elements()?.len() as i32),
    }
}

fn product_size<'a>(
    sets: impl Iterator<Item = &'a Value>,
    overflow: impl Fn() -> Error,
) -> Result<i32> {
    let mut size: i64 = 1;
    for set in sets {
        size *= i64::from(cardinality(set)?);
        if size > i64::from(i32::MAX) {
            return Err(overflow());
        }
    }
    Ok(size as i32)
}

#[cfg(test)]
mod tests {
    use tla_value::{LazySet, Value};

    use crate::stdlib::testing::{call, error, int, ints, tuple};

    fn lazy(set: LazySet) -> Value {
        Value::lazy(set)
    }

    fn is_finite(value: Value) -> bool {
        call("FiniteSets", "IsFiniteSet", &[value]).unwrap().as_bool().unwrap()
    }

    fn cardinality(value: Value) -> i32 {
        call("FiniteSets", "Cardinality", &[value]).unwrap().as_int().unwrap()
    }

    #[test]
    fn tells_finite_sets_like_tlc() {
        assert!(is_finite(ints(&[1, 2])));
        assert!(is_finite(tuple(&[1])));
        assert!(!is_finite(lazy(LazySet::Nat)));
        assert!(!is_finite(lazy(LazySet::Any)));
        assert!(is_finite(lazy(LazySet::Seq(Value::empty_set()))));
        assert!(!is_finite(lazy(LazySet::Seq(ints(&[1])))));
        assert!(is_finite(lazy(LazySet::Subset(Value::Interval(1, 100)))));
        let constant = lazy(LazySet::FuncSet { domain: lazy(LazySet::Nat), range: ints(&[1]) });
        assert!(is_finite(constant));
        let product = lazy(LazySet::Product(vec![Value::empty_set(), lazy(LazySet::Int)].into()));
        assert!(is_finite(product));
        assert!(is_finite(lazy(LazySet::Cap(lazy(LazySet::Nat), ints(&[1])))));
        assert!(!is_finite(lazy(LazySet::Minus(lazy(LazySet::Nat), ints(&[1])))));
        assert_eq!(
            error("FiniteSets", "IsFiniteSet", &[int(1)]),
            "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value),\nbut it produced the following error:\nAttempted to check if the integer 1 is a finite set."
        );
    }

    #[test]
    fn counts_like_tlc() {
        assert_eq!(cardinality(ints(&[1, 2, 3])), 3);
        assert_eq!(cardinality(Value::Interval(5, 1)), 0);
        assert_eq!(cardinality(lazy(LazySet::Subset(Value::Interval(1, 4)))), 16);
        let functions =
            lazy(LazySet::FuncSet { domain: Value::Interval(1, 3), range: ints(&[0, 1]) });
        assert_eq!(cardinality(functions), 8);
        let constant = lazy(LazySet::FuncSet { domain: lazy(LazySet::Nat), range: ints(&[1]) });
        assert_eq!(cardinality(constant), 1);
        let product = lazy(LazySet::Product(vec![Value::empty_set(), lazy(LazySet::Nat)].into()));
        assert_eq!(cardinality(product), 0);
        assert_eq!(
            error("FiniteSets", "Cardinality", &[lazy(LazySet::Nat)]),
            "Attempted to compute cardinality of the value\nNat"
        );
        assert_eq!(
            error("FiniteSets", "Cardinality", &[int(1)]),
            "Attempted to compute cardinality of the value\n1"
        );
        assert_eq!(
            error("FiniteSets", "Cardinality", &[lazy(LazySet::Subset(Value::Interval(1, 31)))]),
            "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value),\nbut it produced the following error:\nOverflow when computing the number of elements in:\nSUBSET (1..31)"
        );
    }
}
