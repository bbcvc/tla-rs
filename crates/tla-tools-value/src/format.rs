//! TLC's printed form of values, ported from tla-ts `formatValue`.

use std::fmt;

use crate::set::sort_like_tlc;
use crate::{LazySet, Result, Value};

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

impl Value {
    /// The value as TLC prints it in an error message. TLC normalizes a set enumeration to print
    /// it, so printing fails where sorting the enumeration fails, as on `{1, "a"}`.
    pub fn text(&self) -> Result<String> {
        self.check_printable()?;
        Ok(self.to_string())
    }

    /// Fails where printing the value would make TLC sort a set enumeration it can't sort.
    pub(crate) fn check_printable(&self) -> Result<()> {
        match self {
            Value::Set(elements) | Value::Tuple(elements) => {
                elements.iter().try_for_each(Value::check_printable)
            }
            Value::MixedSet(elements) => {
                sort_like_tlc(elements)?.iter().try_for_each(Value::check_printable)
            }
            Value::Func(func) => {
                func.keys.iter().chain(func.values.iter()).try_for_each(Value::check_printable)
            }
            // A lazy function TLC can't enumerate prints without its values.
            Value::LazyFunc(_) => {
                self.materialize().map_or(Ok(()), |function| function.check_printable())
            }
            Value::Lazy(set) => match expanded(self, set) {
                Some(elements) => elements.check_printable(),
                None => match &**set {
                    LazySet::Subset(base)
                    | LazySet::Seq(base)
                    | LazySet::Filtered { base, .. }
                    | LazySet::Union(base) => base.check_printable(),
                    LazySet::FuncSet { domain: left, range: right }
                    | LazySet::Cup(left, right)
                    | LazySet::Cap(left, right)
                    | LazySet::Minus(left, right) => {
                        left.check_printable()?;
                        right.check_printable()
                    }
                    LazySet::RecordSet(fields) => {
                        fields.iter().try_for_each(|(_, set)| set.check_printable())
                    }
                    LazySet::Product(factors) => {
                        factors.iter().try_for_each(Value::check_printable)
                    }
                    LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => Ok(()),
                },
            },
            Value::Bool(_)
            | Value::Int(_)
            | Value::Str(_)
            | Value::Model(_)
            | Value::Interval(..) => Ok(()),
        }
    }
}

/// Fails where TLC fails to print one of `values` in an error message, before it builds the
/// message.
pub(crate) fn printable(values: &[&Value]) -> Result<()> {
    values.iter().try_for_each(|value| value.check_printable())
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

    /// tla-ts's NormalizationCases: TLC normalizes a set enumeration to print it, so an error
    /// that prints `{1, "a"}` fails as sorting it does.
    #[test]
    fn fails_to_print_a_set_enumeration_it_cant_sort() {
        let mixed = Value::set(vec![Value::Int(1), Value::str("a")]).unwrap();
        let sorting = "Attempted to compare string \"a\" with non-string:\n1";
        assert_eq!(mixed.text().unwrap_err().0, sorting);
        assert_eq!(Value::tuple(vec![mixed.clone()]).text().unwrap_err().0, sorting);
        assert_eq!(mixed.equals(&Value::Int(1)).unwrap_err().0, sorting);
        assert_eq!(Value::Int(1).equals(&mixed).unwrap_err().0, sorting);
        assert_eq!(Value::Int(1).text().unwrap(), "1");
        let subsets = Value::lazy(LazySet::Subset(Value::Interval(1, 2)));
        assert_eq!(subsets.text().unwrap(), "{{}, {1}, {2}, {1, 2}}");
    }
}
