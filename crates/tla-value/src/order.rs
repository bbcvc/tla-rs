//! TLC's ordering and equality, ported from tla-ts `compareValues` and `valuesEqual`.
//!
//! The order sorts sets and function domains, and so decides what `CHOOSE` returns: model
//! values first, then integers by value, strings by when TLC first interns them (see [`crate::set_order`]), `FALSE`
//! before `TRUE`, sets by size and then element by element, and functions by domain size, then
//! keys, then values. Values of kinds TLC can't compare, such as an integer and a string, are an
//! error rather than an order.

use std::cmp::Ordering;

use crate::format::printable;
use crate::{LazySet, Result, Value, fail, model_type};

/// Fails as TLC does when a typed model value meets a value of another type.
fn check_model_types(left: &Value, right: &Value, is_equality: bool) -> Result<()> {
    let type_of = |value: &Value| match value {
        Value::Model(name) => model_type(*name),
        _ => None,
    };
    let (left_type, right_type) = (type_of(left), type_of(right));
    if left_type.is_none() && right_type.is_none() {
        return Ok(());
    }
    let action = if is_equality { "check equality of" } else { "compare" };
    match (left, right) {
        (Value::Model(_), Value::Model(_)) => {
            if left_type.is_none() || right_type.is_none() || left_type == right_type {
                return Ok(());
            }
            fail!(
                [left, right],
                "Attempted to {action} the differently-typed model values {left} and {right}"
            )
        }
        (Value::Model(_), _) if left_type.is_some() => {
            fail!(
                [left, right],
                "Attempted to {action} the typed model value {left} and non-model value\n{right}"
            )
        }
        _ => fail!(
            [right, left],
            "Attempted to {action} the typed model value {right} and the non-model value\n{left}"
        ),
    }
}

/// The name of a set TLC implements in Java, which compares only with sets of its own class.
fn overridden(value: &Value) -> Option<&'static str> {
    match value {
        Value::Lazy(set) => match **set {
            LazySet::Nat => Some("Nat"),
            LazySet::Int => Some("Int"),
            LazySet::String => Some("STRING"),
            LazySet::Any => Some("Any"),
            LazySet::Seq(_) => Some("Seq"),
            _ => None,
        },
        _ => None,
    }
}

fn compare_overridden(left: &Value, right: &Value, verb: &str) -> Result<Ordering> {
    let Some(left_name) = overridden(left) else {
        // TLC prints the set strictly, enumerating it, which fails as enumerating it fails.
        let is_combined = matches!(
            left,
            Value::Lazy(set) if matches!(
                **set,
                LazySet::Cup(..) | LazySet::Cap(..) | LazySet::Minus(..) | LazySet::Filtered { .. } | LazySet::Union(_)
            )
        );
        let shown = match left.is_enumerable() || is_combined {
            true => Value::Set(left.elements()?),
            false => left.clone(),
        };
        fail!([shown, right], "Attempted to {verb} the set {shown} with the value:\n{right}")
    };
    let Some(right_name) = overridden(right) else {
        fail!(
            [left, right],
            "Attempted to compare overridden value {left} with non-overridden value:\n{right}"
        )
    };
    match (left_name, right_name) {
        ("Seq", "Seq") => {
            let (Value::Lazy(left), Value::Lazy(right)) = (left, right) else { unreachable!() };
            let (LazySet::Seq(left), LazySet::Seq(right)) = (&**left, &**right) else {
                unreachable!()
            };
            left.compare(right)
        }
        (left_name, right_name) if left_name == right_name && left_name != "Any" => {
            Ok(Ordering::Equal)
        }
        ("Nat", "Int") => Ok(Ordering::Less),
        ("Int", "Nat") => Ok(Ordering::Greater),
        _ => fail!([left, right], "Attempted to compare {left} with the value\n{right}"),
    }
}

fn interval_size(low: i32, high: i32) -> i64 {
    (i64::from(high) - i64::from(low) + 1).max(0)
}

impl Value {
    /// TLC's total order on the values it can compare.
    pub fn compare(&self, other: &Value) -> Result<Ordering> {
        use Value::{Bool, Int, Interval, Model, Str};
        match (self, other) {
            (Model(left), Model(right)) => {
                check_model_types(self, other, false)?;
                Ok(left.cmp(right))
            }
            (Model(_), _) => {
                check_model_types(self, other, false)?;
                Ok(Ordering::Less)
            }
            (_, Model(_)) => {
                check_model_types(self, other, false)?;
                Ok(Ordering::Greater)
            }
            (Int(left), Int(right)) => Ok(left.cmp(right)),
            (Str(left), Str(right)) => Ok(left.cmp(right)),
            (Bool(left), Bool(right)) => Ok(left.cmp(right)),
            (Interval(low, high), Interval(other_low, other_high)) => {
                let (size, other_size) =
                    (interval_size(*low, *high), interval_size(*other_low, *other_high));
                if size != other_size || size == 0 {
                    return Ok(size.cmp(&other_size));
                }
                Ok(low.cmp(other_low))
            }
            _ if self.is_function() && other.is_function() => {
                compare_functions(self, other, "compare")
            }
            _ if self.is_set() && other.is_set() => {
                if overridden(self).is_some() || overridden(other).is_some() {
                    return compare_overridden(self, other, "compare");
                }
                compare_elements(&self.elements()?, &other.elements()?)
            }
            _ => Err(mismatch(self, other)),
        }
    }

    /// TLC's equality. Comparing values of different kinds is an error, except that a model
    /// value differs from everything but itself.
    pub fn equals(&self, other: &Value) -> Result<bool> {
        use Value::{Bool, Int, Model, Str};
        self.cache_elements();
        match (self, other) {
            (Model(left), Model(right)) => {
                check_model_types(self, other, true)?;
                Ok(left == right)
            }
            (Model(_), _) | (_, Model(_)) => {
                check_model_types(self, other, true)?;
                Ok(false)
            }
            (Int(left), Int(right)) => Ok(left == right),
            (Str(left), Str(right)) => Ok(left == right),
            (Bool(left), Bool(right)) => Ok(left == right),
            (Int(_) | Str(_) | Bool(_), _) => {
                let kind = self.kind();
                fail!(
                    [self, other],
                    "Attempted to check equality of {kind} {self} with non-{kind}:\n{other}"
                )
            }
            _ if self.is_function() && other.is_function() => {
                Ok(compare_functions(self, other, "check equality of")? == Ordering::Equal)
            }
            _ if self.is_set() && other.is_set() => set_equals(self, other),
            _ => fail!(
                [self, other],
                "Attempted to check equality of {} {self} with {} {other}",
                self.kind(),
                other.kind()
            ),
        }
    }
}

fn compare_elements(left: &[Value], right: &[Value]) -> Result<Ordering> {
    if left.len() != right.len() {
        return Ok(left.len().cmp(&right.len()));
    }
    for (left, right) in left.iter().zip(right) {
        let ordering = left.compare(right)?;
        if ordering != Ordering::Equal {
            return Ok(ordering);
        }
    }
    Ok(Ordering::Equal)
}

/// Compares two functions: by domain size, then keys, then values.
fn compare_functions(left: &Value, right: &Value, verb: &str) -> Result<Ordering> {
    // TLC sorts a function it compares.
    for function in [left, right] {
        if let Value::Func(func) = function {
            func.normalize();
        }
    }
    match (left, right) {
        (Value::Tuple(left), Value::Tuple(right)) => compare_elements(left, right),
        (Value::LazyFunc(_), _) => compare_functions(&left.materialize()?, right, verb),
        (_, Value::LazyFunc(_)) => compare_functions(left, &right.materialize()?, verb),
        _ => {
            let (left_keys, left_values) = left.entries();
            let (right_keys, right_values) = right.entries();
            // TLC compares a record only with another record.
            let is_record = |keys: &[Value]| keys.iter().all(|key| matches!(key, Value::Str(_)));
            let is_mismatch = !left_keys.is_empty()
                && !right_keys.is_empty()
                && is_record(&left_keys) != is_record(&right_keys);
            if is_mismatch && is_record(&left_keys) {
                fail!(
                    [left, right],
                    "Attempted to {verb} record:\n{left}\nwith non-record\n{right}"
                );
            }
            // Any other function compares its size first, as TLC's FcnRcdValue does, so a tuple
            // differs from a record of another size without comparing their keys.
            if left_keys.len() != right_keys.len() {
                return Ok(left_keys.len().cmp(&right_keys.len()));
            }
            for (left, right) in left_keys.iter().zip(right_keys.iter()) {
                let ordering = left.compare(right)?;
                if ordering != Ordering::Equal {
                    return Ok(ordering);
                }
            }
            compare_elements(&left_values, &right_values)
        }
    }
}

/// TLC's error comparing values of different kinds, worded by the class of the left one.
fn mismatch(left: &Value, right: &Value) -> crate::Error {
    if let Err(error) = printable(&[left, right]) {
        return error;
    }
    let message = match left {
        Value::Bool(_) | Value::Int(_) | Value::Str(_) => {
            let kind = left.kind();
            format!("Attempted to compare {kind} {left} with non-{kind}:\n{right}")
        }
        Value::Func(_) if left.kind() == "record" => {
            format!("Attempted to compare record:\n{left}\nwith non-record\n{right}")
        }
        _ if left.is_function() => {
            format!("Attempted to compare the function {left} with the value:\n{right}")
        }
        _ => format!("Attempted to compare the set {left} with the value:\n{right}"),
    };
    crate::Error(message)
}

fn set_equals(left: &Value, right: &Value) -> Result<bool> {
    use LazySet::{FuncSet, Product, RecordSet, Subset};
    if let (Value::Interval(low, high), Value::Interval(other_low, other_high)) = (left, right) {
        let (size, other_size) =
            (interval_size(*low, *high), interval_size(*other_low, *other_high));
        return Ok(size == other_size && (size == 0 || low == other_low));
    }
    if let (Value::Lazy(left_set), Value::Lazy(right_set)) = (left, right) {
        match (&**left_set, &**right_set) {
            (Subset(left), Subset(right)) => return left.equals(right),
            (FuncSet { domain, range }, FuncSet { domain: other_domain, range: other_range }) => {
                let (is_unit, is_other_unit) = (domain.is_empty()?, other_domain.is_empty()?);
                if is_unit || is_other_unit {
                    return Ok(is_unit == is_other_unit);
                }
                let (is_empty, is_other_empty) = (range.is_empty()?, other_range.is_empty()?);
                if is_empty || is_other_empty {
                    return Ok(is_empty == is_other_empty);
                }
                return Ok(domain.equals(other_domain)? && range.equals(other_range)?);
            }
            (RecordSet(fields), RecordSet(other_fields)) => {
                if left.is_empty()? {
                    return right.is_empty();
                }
                if right.is_empty()? {
                    return Ok(false);
                }
                if fields.len() != other_fields.len() {
                    return Ok(false);
                }
                for ((name, set), (other_name, other_set)) in fields.iter().zip(other_fields.iter())
                {
                    if name != other_name || !set.equals(other_set)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            (Product(factors), Product(other_factors)) => {
                if left.is_empty()? {
                    return right.is_empty();
                }
                if right.is_empty()? {
                    return Ok(false);
                }
                if factors.len() != other_factors.len() {
                    return Ok(false);
                }
                for (factor, other) in factors.iter().zip(other_factors.iter()) {
                    if !factor.equals(other)? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            _ => {}
        }
    }
    if overridden(left).is_some() || overridden(right).is_some() {
        return Ok(compare_overridden(left, right, "check equality of")? == Ordering::Equal);
    }
    let (left, right) = (left.elements()?, right.elements()?);
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right.iter()) {
        if !left.equals(right)? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use crate::Value;

    fn int(value: i32) -> Value {
        Value::Int(value)
    }

    #[test]
    fn orders_sets_by_size_first() {
        let small = Value::set(vec![int(9)]).unwrap();
        let large = Value::set(vec![int(1), int(2)]).unwrap();
        assert_eq!(small.compare(&large).unwrap(), Ordering::Less);
        assert_eq!(Value::Interval(1, 2).compare(&large).unwrap(), Ordering::Equal);
    }

    #[test]
    fn equates_representations() {
        let tuple = Value::tuple(vec![Value::str("a"), Value::str("b")]);
        let function =
            Value::function(vec![(int(2), Value::str("b")), (int(1), Value::str("a"))]).unwrap();
        assert!(matches!(function, Value::Tuple(_)));
        assert!(tuple.equals(&function).unwrap());
        assert!(
            Value::Interval(1, 3)
                .equals(&Value::set(vec![int(3), int(1), int(2)]).unwrap())
                .unwrap()
        );
        assert!(Value::Interval(5, 1).equals(&Value::empty_set()).unwrap());
    }

    #[test]
    fn fails_where_tlc_fails() {
        assert!(int(1).equals(&Value::str("a")).is_err());
        assert!(Value::empty_set().equals(&Value::empty_tuple()).is_err());
        assert!(!Value::model("m").equals(&int(1)).unwrap());
        assert!(Value::model("A_m").equals(&int(1)).is_err());
        assert_eq!(Value::model("m").compare(&int(1)).unwrap(), Ordering::Less);
    }
}
