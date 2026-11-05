//! How `Print`, `PrintT`, and `ToString` print values, ported from tla-ts `formatValue` in its
//! strict mode.
//!
//! These operators enumerate a lazy set that TLC prints element by element even when that
//! fails, where an error message prints such a set symbolically instead. `ToString` prints a
//! record in the order its fields are written, and `Print` and `PrintT` print it normalized,
//! with its fields sorted.

use std::fmt::Write;

use tla_tools_value::{LazySet, Result, Value};

use crate::stdlib::finite_sets::cardinality;

/// TLC prints `SUBSET S` element by element when `S` has at most this many elements.
const MAXIMUM_EXPANDED_SUBSET_BASE: i32 = 6;
/// TLC prints a set of functions, records, or tuples element by element up to this size.
const MAXIMUM_EXPANDED_PRODUCT: f64 = 1999.0;

/// The text TLC prints for a value in `ToString`.
pub(crate) fn strict_text(value: &Value) -> Result<String> {
    let mut text = String::new();
    write_value(&mut text, value, false)?;
    Ok(text)
}

/// The text TLC prints for a value in `Print` and `PrintT`, which normalize it first.
pub(crate) fn normalized_text(value: &Value) -> Result<String> {
    let mut text = String::new();
    write_value(&mut text, value, true)?;
    Ok(text)
}

fn write_list(
    text: &mut String,
    items: &[Value],
    separator: &str,
    is_normalized: bool,
) -> Result<()> {
    for (index, item) in items.iter().enumerate() {
        if index > 0 {
            text.push_str(separator);
        }
        write_value(text, item, is_normalized)?;
    }
    Ok(())
}

/// FcnRcdValue#isName: letters, decimal digits, and underscores, with at least one letter.
fn is_field_name(name: &str) -> bool {
    name.chars().all(|char| char.is_alphanumeric() || char == '_')
        && name.chars().any(char::is_alphabetic)
        && !(name.len() >= 4 && (name.starts_with("WF_") || name.starts_with("SF_")))
}

fn write_value(text: &mut String, value: &Value, is_normalized: bool) -> Result<()> {
    match value {
        Value::Set(elements) => {
            text.push('{');
            write_list(text, elements, ", ", is_normalized)?;
            text.push('}');
        }
        Value::MixedSet(_) => write_value(text, &Value::Set(value.elements()?), is_normalized)?,
        Value::Tuple(items) => {
            text.push_str("<<");
            write_list(text, items, ", ", is_normalized)?;
            text.push_str(">>");
        }
        Value::Func(func) => {
            let is_record = func
                .keys
                .iter()
                .all(|key| matches!(key, Value::Str(name) if is_field_name(name.as_str())));
            let (open, separator, divider, close) =
                if is_record { ("[", ", ", " |-> ", "]") } else { ("(", " @@ ", " :> ", ")") };
            let sorted = func.keys.iter().zip(func.values.iter());
            let entries: Box<dyn Iterator<Item = (&Value, &Value)>> = if is_record && !is_normalized
            {
                Box::new(func.written_entries())
            } else {
                Box::new(sorted)
            };
            text.push_str(open);
            for (index, (key, value)) in entries.enumerate() {
                if index > 0 {
                    text.push_str(separator);
                }
                match key {
                    Value::Str(name) if is_record => text.push_str(name.as_str()),
                    _ => write_value(text, key, is_normalized)?,
                }
                text.push_str(divider);
                write_value(text, value, is_normalized)?;
            }
            text.push_str(close);
        }
        // FcnLambdaValue#toString prints a function it fails to enumerate symbolically. TLC
        // normalizes its domain to print it, but evaluates its values afterward.
        Value::LazyFunc(_) => match value.materialize() {
            Ok(function) => write_value(text, &function, false)?,
            Err(_) => write!(text, "{value}").expect("writing to a string succeeds"),
        },
        Value::Lazy(set) => match expanded(value, set)? {
            Some(elements) => write_value(text, &elements, is_normalized)?,
            None => write_lazy(text, set, is_normalized)?,
        },
        _ => write!(text, "{value}").expect("writing to a string succeeds"),
    }
    Ok(())
}

/// The elements of a lazy set if TLC prints it element by element.
fn expanded(value: &Value, set: &LazySet) -> Result<Option<Value>> {
    let size = match set {
        LazySet::Subset(base) => {
            let is_small = cardinality(base)? <= MAXIMUM_EXPANDED_SUBSET_BASE;
            return Ok(is_small.then(|| value.elements()).transpose()?.map(Value::Set));
        }
        LazySet::Cup(..)
        | LazySet::Cap(..)
        | LazySet::Minus(..)
        | LazySet::Filtered { .. }
        | LazySet::Union(_) => return Ok(Some(Value::Set(value.elements()?))),
        LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => {
            return Ok(None);
        }
        LazySet::FuncSet { domain, .. } if domain.is_enumerable() && cardinality(domain)? == 0 => {
            return Ok(Some(Value::Set(vec![Value::empty_tuple()].into())));
        }
        LazySet::FuncSet { domain, range } => {
            f64::from(cardinality(range)?).powf(f64::from(cardinality(domain)?))
        }
        LazySet::RecordSet(fields) => product_size(fields.iter().map(|(_, set)| set))?,
        LazySet::Product(factors) => product_size(factors.iter())?,
    };
    if size == 0.0 {
        return Ok(Some(Value::empty_set()));
    }
    Ok((size <= MAXIMUM_EXPANDED_PRODUCT).then(|| value.elements()).transpose()?.map(Value::Set))
}

/// The size of a product of sets, which TLC stops sizing once it is 0.
fn product_size<'a>(sets: impl Iterator<Item = &'a Value>) -> Result<f64> {
    let mut size = 1.0;
    for set in sets {
        if size == 0.0 {
            break;
        }
        size *= f64::from(cardinality(set)?);
    }
    Ok(size)
}

fn write_lazy(text: &mut String, set: &LazySet, is_normalized: bool) -> Result<()> {
    match set {
        LazySet::Subset(base) => {
            if matches!(base, Value::Interval(..)) {
                text.push_str("SUBSET (");
                write_value(text, base, is_normalized)?;
                text.push(')');
            } else {
                text.push_str("SUBSET ");
                write_value(text, base, is_normalized)?;
            }
        }
        LazySet::FuncSet { domain, range } => {
            text.push('[');
            write_value(text, domain, is_normalized)?;
            text.push_str(" -> ");
            write_value(text, range, is_normalized)?;
            text.push(']');
        }
        LazySet::RecordSet(fields) => {
            text.push('[');
            for (index, (name, set)) in fields.iter().enumerate() {
                if index > 0 {
                    text.push_str(", ");
                }
                text.push_str(name.as_str());
                text.push_str(": ");
                write_value(text, set, is_normalized)?;
            }
            text.push(']');
        }
        LazySet::Product(factors) => {
            text.push('(');
            write_list(text, factors, " \\X ", is_normalized)?;
            text.push(')');
        }
        LazySet::Seq(base) => {
            text.push_str("Seq(");
            write_value(text, base, is_normalized)?;
            text.push(')');
        }
        _ => write!(text, "{}", Value::lazy(set.clone())).expect("writing to a string succeeds"),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use tla_tools_value::{LazySet, Symbol, Value};

    use super::{normalized_text, strict_text};
    use crate::stdlib::testing::ints;

    fn lazy(set: LazySet) -> Value {
        Value::lazy(set)
    }

    fn text(value: &Value) -> String {
        strict_text(value).unwrap()
    }

    #[test]
    fn prints_lazy_sets_like_tlc() {
        assert_eq!(text(&Value::Interval(3, 1)), "{}");
        assert_eq!(text(&Value::tuple(vec![Value::Interval(3, 1)])), "<<{}>>");
        assert_eq!(text(&lazy(LazySet::Subset(ints(&[1])))), "{{}, {1}}");
        assert_eq!(text(&lazy(LazySet::Subset(Value::Interval(1, 7)))), "SUBSET (1..7)");
        let nested = lazy(LazySet::Subset(lazy(LazySet::Subset(Value::Interval(1, 3)))));
        assert_eq!(text(&nested), "SUBSET {{}, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}}");
        assert_eq!(text(&lazy(LazySet::Subset(Value::Interval(3, 1)))), "{{}}");
        let small = lazy(LazySet::FuncSet { domain: ints(&[1]), range: ints(&[2, 3]) });
        assert_eq!(text(&small), "{<<2>>, <<3>>}");
        let large =
            lazy(LazySet::FuncSet { domain: Value::Interval(1, 2), range: Value::Interval(1, 45) });
        assert_eq!(text(&large), "[1..2 -> 1..45]");
        let unit = lazy(LazySet::FuncSet { domain: Value::empty_set(), range: ints(&[1]) });
        assert_eq!(text(&unit), "{<<>>}");
        let records = lazy(LazySet::RecordSet(vec![(Symbol::intern("a"), ints(&[1, 2]))].into()));
        assert_eq!(text(&records), "{[a |-> 1], [a |-> 2]}");
        let many =
            lazy(LazySet::RecordSet(vec![(Symbol::intern("a"), Value::Interval(1, 2000))].into()));
        assert_eq!(text(&many), "[a: 1..2000]");
        let product = lazy(LazySet::Product(vec![ints(&[1]), ints(&[2, 3])].into()));
        assert_eq!(text(&product), "{<<1, 2>>, <<1, 3>>}");
        let wide =
            lazy(LazySet::Product(vec![Value::Interval(1, 40), Value::Interval(1, 50)].into()));
        assert_eq!(text(&wide), "(1..40 \\X 1..50)");
        let empty = lazy(LazySet::Product(vec![Value::empty_set(), lazy(LazySet::Nat)].into()));
        assert_eq!(text(&empty), "{}");
        assert_eq!(text(&lazy(LazySet::Seq(lazy(LazySet::Nat)))), "Seq(Nat)");
    }

    #[test]
    fn fails_to_print_what_it_cant_enumerate() {
        assert!(strict_text(&lazy(LazySet::Subset(lazy(LazySet::Nat)))).is_err());
        let functions = lazy(LazySet::FuncSet { domain: lazy(LazySet::Nat), range: ints(&[1]) });
        assert!(strict_text(&functions).is_err());
        assert!(strict_text(&Value::set(vec![Value::Int(1), Value::str("a")]).unwrap()).is_err());
    }

    /// tla-ts's NormalizationCases: `ToString` prints a record in the order its fields are
    /// written, and `Print` normalizes it first, sorting its fields as TLC interned their names.
    #[test]
    fn prints_records_as_written_or_normalized() {
        let later = Symbol::intern("print_order_later");
        let earlier = Symbol::intern("print_order_earlier");
        let record = Value::record(vec![(earlier, Value::Int(1)), (later, Value::Int(2))]);
        let nested = Value::tuple(vec![record.clone()]);
        assert_eq!(text(&nested), "<<[print_order_earlier |-> 1, print_order_later |-> 2]>>");
        assert_eq!(
            normalized_text(&nested).unwrap(),
            "<<[print_order_later |-> 2, print_order_earlier |-> 1]>>"
        );
    }
}
