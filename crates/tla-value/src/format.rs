//! TLC's printed form of values, ported from tla-ts `formatValue`.

use std::fmt;

use crate::{LazySet, Value};

/// TLC prints `SUBSET S` element by element when `S` has at most this many elements.
const MAXIMUM_EXPANDED_SUBSET_BASE: i32 = 6;
/// TLC prints a set of functions, records, or tuples element by element up to this size.
const MAXIMUM_EXPANDED_PRODUCT: i64 = 1999;

fn write_list(formatter: &mut fmt::Formatter<'_>, items: &[Value], separator: &str) -> fmt::Result {
    for (index, item) in items.iter().enumerate() {
        if index > 0 {
            formatter.write_str(separator)?;
        }
        write!(formatter, "{item}")?;
    }
    Ok(())
}

/// FcnRcdValue#isName: letters, decimal digits, and underscores, with at least one letter.
fn is_field_name(name: &str) -> bool {
    name.chars().all(|char| char.is_alphanumeric() || char == '_')
        && name.chars().any(char::is_alphabetic)
        && !(name.len() >= 4 && (name.starts_with("WF_") || name.starts_with("SF_")))
}

fn write_string(formatter: &mut fmt::Formatter<'_>, text: &str) -> fmt::Result {
    formatter.write_str("\"")?;
    for char in text.chars() {
        match char {
            '\\' => formatter.write_str("\\\\")?,
            '"' => formatter.write_str("\\\"")?,
            '\n' => formatter.write_str("\\n")?,
            '\t' => formatter.write_str("\\t")?,
            _ => write!(formatter, "{char}")?,
        }
    }
    formatter.write_str("\"")
}

/// The elements of a lazy set if TLC prints it element by element.
fn expanded(value: &Value, set: &LazySet) -> Option<Value> {
    let size = |sets: &[&Value]| -> Option<i64> {
        sets.iter().try_fold(1i64, |size, set| {
            Some(size.saturating_mul(i64::from(set.cardinality().ok()?)))
        })
    };
    let is_small = match set {
        LazySet::Subset(base) => base.cardinality().ok()? <= MAXIMUM_EXPANDED_SUBSET_BASE,
        LazySet::FuncSet { domain, range } => {
            let (domain, range) = (domain.cardinality().ok()?, range.cardinality().ok()?);
            domain == 0
                || i64::from(range)
                    .checked_pow(domain as u32)
                    .is_some_and(|size| size <= MAXIMUM_EXPANDED_PRODUCT)
        }
        LazySet::RecordSet(fields) => {
            size(&fields.iter().map(|(_, set)| set).collect::<Vec<_>>())?
                <= MAXIMUM_EXPANDED_PRODUCT
        }
        LazySet::Product(factors) => {
            size(&factors.iter().collect::<Vec<_>>())? <= MAXIMUM_EXPANDED_PRODUCT
        }
        LazySet::Cup(..)
        | LazySet::Cap(..)
        | LazySet::Minus(..)
        | LazySet::Filtered { .. }
        | LazySet::Union(_) => true,
        LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => false,
    };
    (is_small && value.is_enumerable()).then(|| value.elements().ok().map(Value::Set)).flatten()
}

fn write_lazy(formatter: &mut fmt::Formatter<'_>, set: &LazySet) -> fmt::Result {
    match set {
        LazySet::Subset(base @ Value::Interval(..)) => write!(formatter, "SUBSET ({base})"),
        LazySet::Subset(base) => write!(formatter, "SUBSET {base}"),
        LazySet::FuncSet { domain, range } => write!(formatter, "[{domain} -> {range}]"),
        LazySet::RecordSet(fields) => {
            formatter.write_str("[")?;
            for (index, (name, set)) in fields.iter().enumerate() {
                let separator = if index > 0 { ", " } else { "" };
                write!(formatter, "{separator}{name}: {set}")?;
            }
            formatter.write_str("]")
        }
        LazySet::Product(factors) => {
            formatter.write_str("(")?;
            write_list(formatter, factors, " \\X ")?;
            formatter.write_str(")")
        }
        LazySet::Seq(base) => write!(formatter, "Seq({base})"),
        LazySet::Nat => formatter.write_str("Nat"),
        LazySet::Int => formatter.write_str("Int"),
        LazySet::String => formatter.write_str("STRING"),
        LazySet::Any => formatter.write_str("ANY"),
        LazySet::Cup(left, right) => write!(formatter, "{left} \\cup {right}"),
        LazySet::Cap(left, right) => write!(formatter, "{left} \\cap {right}"),
        LazySet::Minus(left, right) => write!(formatter, "{left} \\ {right}"),
        LazySet::Filtered { base, .. } => write!(formatter, "{{x \\in {base} : ...}}"),
        LazySet::Union(base) => write!(formatter, "UNION {base}"),
    }
}

impl fmt::Display for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(value) => formatter.write_str(if *value { "TRUE" } else { "FALSE" }),
            Value::Int(value) => write!(formatter, "{value}"),
            Value::Str(text) => write_string(formatter, text.as_str()),
            Value::Model(name) => formatter.write_str(name.as_str()),
            Value::Set(elements) => {
                formatter.write_str("{")?;
                write_list(formatter, elements, ", ")?;
                formatter.write_str("}")
            }
            Value::MixedSet(elements) => {
                formatter.write_str("{")?;
                write_list(formatter, elements, ", ")?;
                formatter.write_str("}")
            }
            Value::Interval(low, high) if low <= high => write!(formatter, "{low}..{high}"),
            Value::Interval(..) => formatter.write_str("{}"),
            Value::Lazy(set) => match expanded(self, set) {
                Some(elements) => write!(formatter, "{elements}"),
                None => write_lazy(formatter, set),
            },
            Value::Tuple(items) => {
                formatter.write_str("<<")?;
                write_list(formatter, items, ", ")?;
                formatter.write_str(">>")
            }
            Value::Func(func) => {
                let is_record = func
                    .keys
                    .iter()
                    .all(|key| matches!(key, Value::Str(name) if is_field_name(name.as_str())));
                if is_record {
                    formatter.write_str("[")?;
                    for (index, (key, value)) in func.written_entries().enumerate() {
                        let Value::Str(name) = key else { unreachable!() };
                        let separator = if index > 0 { ", " } else { "" };
                        write!(formatter, "{separator}{name} |-> {value}")?;
                    }
                    return formatter.write_str("]");
                }
                formatter.write_str("(")?;
                for (index, (key, value)) in func.keys.iter().zip(func.values.iter()).enumerate() {
                    let separator = if index > 0 { " @@ " } else { "" };
                    write!(formatter, "{separator}{key} :> {value}")?;
                }
                formatter.write_str(")")
            }
            Value::LazyFunc(_) => match self.materialize() {
                Ok(function) => write!(formatter, "{function}"),
                Err(_) => formatter.write_str("<function>"),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{LazySet, Symbol, Value};

    #[test]
    fn prints_like_tlc() {
        let set = Value::set(vec![Value::str("b"), Value::str("a\"")]).unwrap();
        assert!(set.to_string() == "{\"b\", \"a\\\"\"}" || set.to_string() == "{\"a\\\"\", \"b\"}");
        assert_eq!(Value::Interval(1, 3).to_string(), "1..3");
        assert_eq!(Value::Interval(3, 1).to_string(), "{}");
        let function =
            Value::function(vec![(Value::Int(0), Value::TRUE), (Value::Int(2), Value::FALSE)])
                .unwrap();
        assert_eq!(function.to_string(), "(0 :> TRUE @@ 2 :> FALSE)");
        let record = Value::record(vec![(Symbol::intern("a"), Value::Int(1))]);
        assert_eq!(record.to_string(), "[a |-> 1]");
        assert_eq!(
            Value::lazy(LazySet::Subset(Value::Interval(1, 10))).to_string(),
            "SUBSET (1..10)"
        );
        assert_eq!(Value::lazy(LazySet::Seq(Value::lazy(LazySet::Nat))).to_string(), "Seq(Nat)");
    }
}
