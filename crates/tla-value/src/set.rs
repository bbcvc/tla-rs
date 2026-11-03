//! Sets: canonical construction, membership, enumeration in TLC's order, and cardinality.

use std::cmp::Ordering;
use std::sync::Arc;

use crate::{Error, LazySet, Result, Value, bail};

/// Sorts values by [`Value::compare`] and drops duplicates, or fails if two can't be compared.
pub(crate) fn sort_unique(mut elements: Vec<Value>) -> Result<Vec<Value>> {
    let mut failure = None;
    elements.sort_by(|left, right| {
        left.compare(right).unwrap_or_else(|error| {
            failure.get_or_insert(error);
            Ordering::Equal
        })
    });
    if let Some(error) = failure {
        return Err(error);
    }
    let mut unique: Vec<Value> = Vec::with_capacity(elements.len());
    for element in elements {
        if match unique.last() {
            Some(last) => last.compare(&element)? != Ordering::Equal,
            None => true,
        } {
            unique.push(element);
        }
    }
    Ok(unique)
}

/// Finds `value` in values sorted by [`Value::compare`].
pub(crate) fn search(sorted: &[Value], value: &Value) -> Result<std::result::Result<usize, usize>> {
    let (mut low, mut high) = (0, sorted.len());
    while low < high {
        let middle = low + (high - low) / 2;
        match sorted[middle].compare(value)? {
            Ordering::Equal => return Ok(Ok(middle)),
            Ordering::Less => low = middle + 1,
            Ordering::Greater => high = middle,
        }
    }
    Ok(Err(low))
}

fn infinite(set: &Value) -> Error {
    Error(format!("Attempted to enumerate the infinite set {set}"))
}

/// Every choice of one element from each list, the first list varying slowest, which is the
/// order TLC sorts tuples, records, and functions over a shared domain in.
fn choices(lists: &[Arc<[Value]>]) -> Vec<Vec<Value>> {
    let total = lists.iter().map(|list| list.len()).product::<usize>();
    let mut result = Vec::with_capacity(total);
    if total == 0 {
        return result;
    }
    let mut indexes = vec![0; lists.len()];
    loop {
        result.push(indexes.iter().zip(lists).map(|(&index, list)| list[index].clone()).collect());
        let mut position = lists.len();
        loop {
            if position == 0 {
                return result;
            }
            position -= 1;
            indexes[position] += 1;
            if indexes[position] < lists[position].len() {
                break;
            }
            indexes[position] = 0;
        }
    }
}

fn checked_power(base: i64, exponent: i64, set: &Value) -> Result<i32> {
    let mut result: i64 = 1;
    for _ in 0..exponent {
        result =
            result.checked_mul(base).filter(|&value| value <= i64::from(i32::MAX)).ok_or_else(
                || Error(format!("Overflow when computing the number of elements in:\n{set}")),
            )?;
        if result == 0 {
            return Ok(0);
        }
    }
    Ok(result as i32)
}

impl Value {
    /// The set of `elements`. A set whose elements TLC can't sort, such as `{1, "a"}`, is kept
    /// unsorted, as TLC keeps it, and fails only when something has to sort it.
    pub fn set(elements: Vec<Value>) -> Result<Value> {
        match sort_unique(elements.clone()) {
            Ok(sorted) => Ok(Value::Set(sorted.into())),
            Err(_) => {
                let mut unique: Vec<Value> = Vec::with_capacity(elements.len());
                for element in elements {
                    if !unique.iter().any(|known| known.equals(&element).unwrap_or(false)) {
                        unique.push(element);
                    }
                }
                Ok(Value::MixedSet(unique.into()))
            }
        }
    }

    /// Whether TLC can list this set's elements.
    pub fn is_enumerable(&self) -> bool {
        match self {
            Value::Set(_) | Value::MixedSet(_) | Value::Interval(..) => true,
            Value::Lazy(set) => match &**set {
                LazySet::Subset(base) | LazySet::Filtered { base, .. } => base.is_enumerable(),
                LazySet::FuncSet { domain, range } => {
                    domain.is_enumerable() && range.is_enumerable()
                }
                LazySet::RecordSet(fields) => fields.iter().all(|(_, set)| set.is_enumerable()),
                LazySet::Product(factors) => factors.iter().all(Value::is_enumerable),
                LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => {
                    false
                }
                LazySet::Cup(left, right) => left.is_enumerable() && right.is_enumerable(),
                LazySet::Cap(left, right) => left.is_enumerable() || right.is_enumerable(),
                LazySet::Minus(left, _) => left.is_enumerable(),
                LazySet::Union(base) => {
                    base.is_enumerable()
                        && base.elements().is_ok_and(|sets| sets.iter().all(Value::is_enumerable))
                }
            },
            _ => false,
        }
    }

    /// The elements in TLC's order.
    pub fn elements(&self) -> Result<Arc<[Value]>> {
        match self {
            Value::Set(elements) => Ok(elements.clone()),
            Value::MixedSet(elements) => Ok(sort_unique(elements.to_vec())?.into()),
            Value::Interval(low, high) => Ok((*low..=*high).map(Value::Int).collect()),
            Value::Lazy(set) => self.lazy_elements(set),
            _ => bail!("Attempted to enumerate {} {self}, which is not a set", self.kind()),
        }
    }

    fn lazy_elements(&self, set: &LazySet) -> Result<Arc<[Value]>> {
        match set {
            LazySet::Subset(base) => {
                let base = base.elements()?;
                if base.len() > 30 {
                    bail!("Overflow when computing the number of elements in:\n{self}");
                }
                // Combinations of each size in index order are already in TLC's order, since the
                // base is sorted and sets compare by size first.
                let mut subsets = Vec::with_capacity(1 << base.len());
                for size in 0..=base.len() {
                    let mut indexes: Vec<usize> = (0..size).collect();
                    loop {
                        subsets.push(Value::Set(
                            indexes.iter().map(|&index| base[index].clone()).collect(),
                        ));
                        let Some(position) = (0..size)
                            .rev()
                            .find(|&position| indexes[position] < base.len() - size + position)
                        else {
                            break;
                        };
                        indexes[position] += 1;
                        for next in position + 1..size {
                            indexes[next] = indexes[next - 1] + 1;
                        }
                    }
                }
                Ok(subsets.into())
            }
            LazySet::FuncSet { domain, range } => {
                let keys = domain.elements()?;
                let range = range.elements()?;
                let lists = vec![range; keys.len()];
                choices(&lists)
                    .into_iter()
                    .map(|values| Value::function(keys.iter().cloned().zip(values).collect()))
                    .collect()
            }
            LazySet::RecordSet(fields) => {
                let lists =
                    fields.iter().map(|(_, set)| set.elements()).collect::<Result<Vec<_>>>()?;
                let records = choices(&lists).into_iter().map(|values| {
                    Value::record(fields.iter().map(|(name, _)| *name).zip(values).collect())
                });
                Ok(records.collect())
            }
            LazySet::Product(factors) => {
                let lists = factors.iter().map(Value::elements).collect::<Result<Vec<_>>>()?;
                Ok(choices(&lists).into_iter().map(Value::tuple).collect())
            }
            LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => {
                Err(infinite(self))
            }
            LazySet::Cup(left, right) => {
                let mut elements = left.elements()?.to_vec();
                elements.extend(right.elements()?.iter().cloned());
                Ok(sort_unique(elements)?.into())
            }
            LazySet::Cap(left, right) => {
                let (enumerated, other) =
                    if left.is_enumerable() { (left, right) } else { (right, left) };
                self.filter(enumerated, |element| other.contains(element))
            }
            LazySet::Minus(left, right) => {
                self.filter(left, |element| Ok(!right.contains(element)?))
            }
            LazySet::Filtered { base, test } => self.filter(base, |element| test(element)),
            LazySet::Union(base) => {
                let mut elements = Vec::new();
                for set in base.elements()?.iter() {
                    elements.extend(set.elements()?.iter().cloned());
                }
                Ok(sort_unique(elements)?.into())
            }
        }
    }

    fn filter(
        &self,
        base: &Value,
        mut keep: impl FnMut(&Value) -> Result<bool>,
    ) -> Result<Arc<[Value]>> {
        if !base.is_enumerable() {
            return Err(infinite(self));
        }
        let mut kept = Vec::new();
        for element in base.elements()?.iter() {
            if keep(element)? {
                kept.push(element.clone());
            }
        }
        Ok(kept.into())
    }

    pub fn is_empty(&self) -> Result<bool> {
        match self {
            Value::Set(elements) | Value::MixedSet(elements) => Ok(elements.is_empty()),
            Value::Interval(low, high) => Ok(low > high),
            Value::Lazy(set) => match &**set {
                LazySet::Subset(_) | LazySet::Seq(_) => Ok(false),
                LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => Ok(false),
                LazySet::FuncSet { domain, range } => Ok(!domain.is_empty()? && range.is_empty()?),
                LazySet::RecordSet(fields) => {
                    for (_, set) in fields.iter() {
                        if set.is_empty()? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                LazySet::Product(factors) => {
                    for factor in factors.iter() {
                        if factor.is_empty()? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                LazySet::Cup(left, right) => Ok(left.is_empty()? && right.is_empty()?),
                _ => Ok(self.elements()?.is_empty()),
            },
            _ => bail!(
                "Attempted to check whether {} {self} is empty, but it is not a set",
                self.kind()
            ),
        }
    }

    /// `value \in self`.
    pub fn contains(&self, value: &Value) -> Result<bool> {
        match self {
            Value::Set(elements) => Ok(search(elements, value)?.is_ok()),
            Value::MixedSet(elements) => {
                for element in elements.iter() {
                    if element.equals(value)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Value::Interval(low, high) => match value {
                Value::Int(value) => Ok(low <= value && value <= high),
                Value::Model(_) => Ok(false),
                _ => bail!(
                    "Attempted to check if the value:\n{value}\nis in the integer interval {self}"
                ),
            },
            Value::Lazy(set) => self.lazy_contains(set, value),
            _ => bail!(
                "Attempted to check if the value:\n{value}\nis an element of {} {self}",
                self.kind()
            ),
        }
    }

    fn lazy_contains(&self, set: &LazySet, value: &Value) -> Result<bool> {
        if matches!(value, Value::Model(_))
            && !matches!(
                set,
                LazySet::Any
                    | LazySet::Cup(..)
                    | LazySet::Cap(..)
                    | LazySet::Minus(..)
                    | LazySet::Filtered { .. }
                    | LazySet::Union(_)
            )
        {
            return Ok(false);
        }
        match set {
            LazySet::Subset(base) => {
                if !value.is_set() {
                    bail!("Attempted to check if the non-set {value} is an element of {self}");
                }
                value.is_subset_of(base)
            }
            LazySet::FuncSet { domain, range } => {
                if !value.is_function() {
                    bail!(
                        "Attempted to check if the non-function\n{value}\nis an element of the set of functions {self}"
                    );
                }
                if !value.domain()?.equals(domain)? {
                    return Ok(false);
                }
                let function = value.materialize()?;
                let (_, values) = function.entries();
                for item in values.iter() {
                    if !range.contains(item)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            LazySet::RecordSet(fields) => {
                let Value::Func(record) = value else {
                    if value.is_function() {
                        return Ok(false);
                    }
                    bail!(
                        "Attempted to check if the non-record\n{value}\nis an element of the set of records {self}"
                    );
                };
                if record.keys.len() != fields.len() {
                    return Ok(false);
                }
                for (key, item) in record.keys.iter().zip(record.values.iter()) {
                    let Value::Str(name) = key else { return Ok(false) };
                    let Some((_, set)) = fields.iter().find(|(field, _)| field == name) else {
                        return Ok(false);
                    };
                    if !set.contains(item)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            LazySet::Product(factors) => {
                let Value::Tuple(items) = value else {
                    if value.is_function() {
                        return Ok(false);
                    }
                    bail!(
                        "Attempted to check if the non-tuple\n{value}\nis an element of the Cartesian product {self}"
                    );
                };
                if items.len() != factors.len() {
                    return Ok(false);
                }
                for (item, factor) in items.iter().zip(factors.iter()) {
                    if !factor.contains(item)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            LazySet::Seq(base) => match value {
                Value::Tuple(items) => {
                    for item in items.iter() {
                        if !base.contains(item)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                _ => Ok(false),
            },
            LazySet::Nat => match value {
                Value::Int(value) => Ok(*value >= 0),
                _ => bail!("Attempted to check if the value:\n{value}\nis in Nat"),
            },
            LazySet::Int => match value {
                Value::Int(_) => Ok(true),
                _ => bail!("Attempted to check if the value:\n{value}\nis in Int"),
            },
            LazySet::String => Ok(matches!(value, Value::Str(_))),
            LazySet::Any => Ok(true),
            LazySet::Cup(left, right) => Ok(left.contains(value)? || right.contains(value)?),
            LazySet::Cap(left, right) => Ok(left.contains(value)? && right.contains(value)?),
            LazySet::Minus(left, right) => Ok(left.contains(value)? && !right.contains(value)?),
            LazySet::Filtered { base, test } => Ok(base.contains(value)? && test(value)?),
            LazySet::Union(base) => {
                for set in base.elements()?.iter() {
                    if set.contains(value)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
        }
    }

    /// `self \subseteq other`.
    pub fn is_subset_of(&self, other: &Value) -> Result<bool> {
        if let (Value::Lazy(left), Value::Lazy(right)) = (self, other)
            && let (LazySet::Subset(left), LazySet::Subset(right)) = (&**left, &**right)
            && left.is_enumerable()
        {
            return left.is_subset_of(right);
        }
        for element in self.elements()?.iter() {
            if !other.contains(element)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// `Cardinality(self)`.
    pub fn cardinality(&self) -> Result<i32> {
        let overflow =
            || Error(format!("Overflow when computing the number of elements in:\n{self}"));
        match self {
            Value::Interval(low, high) => {
                let size = (i64::from(*high) - i64::from(*low) + 1).max(0);
                i32::try_from(size).map_err(|_| overflow())
            }
            Value::Lazy(set) => match &**set {
                LazySet::Subset(base) => checked_power(2, i64::from(base.cardinality()?), self),
                LazySet::FuncSet { domain, range } => checked_power(
                    i64::from(range.cardinality()?),
                    i64::from(domain.cardinality()?),
                    self,
                ),
                LazySet::RecordSet(fields) => {
                    let sets: Vec<&Value> = fields.iter().map(|(_, set)| set).collect();
                    product_size(&sets, self)
                }
                LazySet::Product(factors) => {
                    product_size(&factors.iter().collect::<Vec<_>>(), self)
                }
                LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => {
                    bail!("Attempted to compute cardinality of the value\n{self}")
                }
                _ => Ok(self.elements()?.len() as i32),
            },
            _ => i32::try_from(self.elements()?.len()).map_err(|_| overflow()),
        }
    }

    /// `self \cup other`, enumerated when both sides are.
    pub fn cup(&self, other: &Value) -> Result<Value> {
        if self.is_enumerable() && other.is_enumerable() {
            if self.is_empty()? {
                return Ok(other.clone());
            }
            let mut elements = self.elements()?.to_vec();
            elements.extend(other.elements()?.iter().cloned());
            return Value::set(elements);
        }
        Ok(Value::lazy(LazySet::Cup(self.clone(), other.clone())))
    }

    /// `self \cap other`, enumerated when either side is.
    pub fn cap(&self, other: &Value) -> Result<Value> {
        let set = Value::lazy(LazySet::Cap(self.clone(), other.clone()));
        if self.is_enumerable() || other.is_enumerable() {
            return Ok(Value::Set(set.elements()?));
        }
        Ok(set)
    }

    /// `self \ other`, enumerated when the left side is.
    pub fn minus(&self, other: &Value) -> Result<Value> {
        let set = Value::lazy(LazySet::Minus(self.clone(), other.clone()));
        if self.is_enumerable() {
            return Ok(Value::Set(set.elements()?));
        }
        Ok(set)
    }

    /// `UNION self`, enumerated when every set in it is.
    pub fn union(&self) -> Result<Value> {
        let set = Value::lazy(LazySet::Union(self.clone()));
        if set.is_enumerable() {
            return Ok(Value::Set(set.elements()?));
        }
        Ok(set)
    }
}

fn product_size(sets: &[&Value], whole: &Value) -> Result<i32> {
    let mut size: i64 = 1;
    for set in sets {
        size = size
            .checked_mul(i64::from(set.cardinality()?))
            .filter(|&size| size <= i64::from(i32::MAX))
            .ok_or_else(|| {
                Error(format!("Overflow when computing the number of elements in:\n{whole}"))
            })?;
    }
    Ok(size as i32)
}

#[cfg(test)]
mod tests {
    use crate::{LazySet, Value};

    fn ints(values: &[i32]) -> Value {
        Value::set(values.iter().map(|&value| Value::Int(value)).collect()).unwrap()
    }

    fn format(value: &Value) -> String {
        value.to_string()
    }

    #[test]
    fn enumerates_lazy_sets_in_tlc_order() {
        let subsets = Value::lazy(LazySet::Subset(ints(&[1, 2, 3])));
        assert_eq!(
            format(&Value::Set(subsets.elements().unwrap())),
            "{{}, {1}, {2}, {3}, {1, 2}, {1, 3}, {2, 3}, {1, 2, 3}}"
        );
        let functions =
            Value::lazy(LazySet::FuncSet { domain: ints(&[1, 2]), range: ints(&[0, 1]) });
        assert_eq!(
            format(&Value::Set(functions.elements().unwrap())),
            "{<<0, 0>>, <<0, 1>>, <<1, 0>>, <<1, 1>>}"
        );
        let product = Value::lazy(LazySet::Product(vec![ints(&[1, 2]), ints(&[3])].into()));
        assert_eq!(product.cardinality().unwrap(), 2);
        assert!(product.contains(&Value::tuple(vec![Value::Int(2), Value::Int(3)])).unwrap());
    }

    #[test]
    fn tests_membership_without_enumerating() {
        let nat = Value::lazy(LazySet::Nat);
        assert!(nat.contains(&Value::Int(5)).unwrap());
        assert!(!nat.contains(&Value::Int(-1)).unwrap());
        let big = Value::lazy(LazySet::Subset(Value::Interval(1, 100)));
        assert!(big.contains(&ints(&[3, 50])).unwrap());
        assert!(!big.contains(&ints(&[0])).unwrap());
        assert!(big.cardinality().is_err());
    }

    #[test]
    fn keeps_unsortable_sets_unsorted() {
        let mixed = Value::set(vec![Value::Int(1), Value::str("a")]).unwrap();
        assert!(matches!(mixed, Value::MixedSet(_)));
        assert!(mixed.contains(&Value::Int(1)).unwrap());
        assert!(mixed.elements().is_err());
    }
}
