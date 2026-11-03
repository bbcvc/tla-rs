//! Sets: canonical construction, membership, enumeration in TLC's order, and cardinality.

use std::cmp::Ordering;
use std::sync::Arc;

use crate::combinations::{Combinations, Make};
use crate::{Error, LazySet, Result, Value, bail, fail};

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

/// Whether TLC implements the set in Java: `Nat`, `Int`, `STRING`, `Seq(S)`, and `Any`, which it
/// can't enumerate.
pub(crate) fn is_overridden(value: &Value) -> bool {
    matches!(
        value,
        Value::Lazy(set)
            if matches!(**set, LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any | LazySet::Seq(_))
    )
}

/// Whether TLC's `Enumerable` interface covers the value: every set but the overridden ones.
pub(crate) fn is_tlc_enumerable(value: &Value) -> bool {
    value.is_set() && !is_overridden(value)
}

/// What kind of value this is, as TLC names it where it doesn't tell functions apart.
pub(crate) fn describe_kind(value: &Value) -> &'static str {
    match value {
        Value::Bool(_) => "boolean",
        Value::Int(_) => "integer",
        Value::Str(_) => "string",
        Value::Model(_) => "model value",
        _ if value.is_set() => "set",
        _ => "function",
    }
}

/// TLC's `ValueVec.sort` of a set enumeration: each element inserted into the sorted prefix by
/// binary search, so that the first comparison that fails is the one TLC makes.
pub(crate) fn sort_like_tlc(elements: &[Value]) -> Result<Vec<Value>> {
    let mut sorted: Vec<Value> = Vec::with_capacity(elements.len());
    'elements: for element in elements {
        let (mut low, mut high) = (0, sorted.len());
        while low < high {
            let middle = low + (high - low) / 2;
            match element.compare(&sorted[middle])? {
                Ordering::Equal => continue 'elements,
                Ordering::Less => high = middle,
                Ordering::Greater => low = middle + 1,
            }
        }
        sorted.insert(low, element.clone());
    }
    Ok(sorted)
}

/// How a set lists the elements of a set it combines: in TLC's order, or as TLC streams them.
pub(crate) type ElementsOf = fn(&Value) -> Result<Arc<[Value]>>;

/// The elements of the sets a set of records or tuples combines, enumerated in turn, stopping at
/// the first empty one, which leaves the combination empty.
fn component_elements(
    sets: &[&Value],
    elements_of: ElementsOf,
    unenumerable: impl Fn(&Value, usize) -> String,
) -> Result<Vec<Arc<[Value]>>> {
    let mut lists = Vec::with_capacity(sets.len());
    for (index, set) in sets.iter().enumerate() {
        if is_overridden(set) {
            return Err(Error(unenumerable(set, index)));
        }
        let elements = elements_of(set)?;
        if elements.is_empty() {
            return Ok(vec![elements]);
        }
        lists.push(elements);
    }
    Ok(lists)
}

/// The elements of `set` that satisfy `test`, without building those of a large set that don't.
fn keep(set: &Value, mut test: impl FnMut(&Value) -> Result<bool>) -> Result<Arc<[Value]>> {
    let mut kept = Vec::new();
    for element in set.enumeration()?.iter() {
        if test(&element)? {
            kept.push(element);
        }
    }
    Ok(kept.into())
}

/// The sets `UNION base` combines, which TLC must be able to enumerate.
pub(crate) fn union_sets(base: &Value, elements_of: ElementsOf) -> Result<Arc<[Value]>> {
    if !is_tlc_enumerable(base) {
        fail!([base], "Attempted to enumerate the nonenumerable set:\nUNION({base})");
    }
    elements_of(base)
}

pub(crate) fn union_set<'a>(base: &Value, set: &'a Value, index: usize) -> Result<&'a Value> {
    if is_tlc_enumerable(set) {
        return Ok(set);
    }
    if index == 0 {
        bail!("Attempted to enumerate UNION(s), but some element of s is nonenumerable.");
    }
    fail!(
        [set, base],
        "Attempted to enumerate the nonenumerable set:\n{set}\nwhen enumerating:\nUNION({base})"
    )
}

/// The first key of keys that form an interval, as TLC keeps the domain of such a function.
fn interval_low(keys: &[Value]) -> Option<i32> {
    let Some(first) = keys.first() else { return Some(1) };
    let Value::Int(first) = *first else { return None };
    let is_interval = keys
        .iter()
        .enumerate()
        .all(|(index, key)| matches!(key, Value::Int(key) if i64::from(*key) == i64::from(first) + index as i64));
    is_interval.then_some(first)
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
    /// as written, as TLC keeps it, and fails only when something has to sort it.
    pub fn set(elements: Vec<Value>) -> Result<Value> {
        // TLC's `ValueVec.sort` compares each element after the first with those before it.
        elements.iter().skip(1).for_each(Value::cache_elements);
        match sort_unique(elements.clone()) {
            Ok(sorted) => Ok(Value::Set(sorted.into())),
            Err(_) => Ok(Value::MixedSet(elements.into())),
        }
    }

    /// Whether TLC can list this set's elements: a set it doesn't implement in Java, and whose
    /// parts it can list, unless an empty part decides the set.
    pub fn is_enumerable(&self) -> bool {
        match self {
            Value::Set(_) | Value::MixedSet(_) | Value::Interval(..) => true,
            Value::Lazy(set) => match &**set {
                LazySet::Subset(base) | LazySet::Filtered { base, .. } => base.is_enumerable(),
                LazySet::FuncSet { domain, range } => {
                    (domain.is_enumerable() && range.is_enumerable())
                        || domain.emptiness() == Some(true)
                        || self.emptiness() == Some(true)
                }
                LazySet::RecordSet(fields) => {
                    fields.iter().all(|(_, set)| set.is_enumerable())
                        || self.emptiness() == Some(true)
                }
                LazySet::Product(factors) => {
                    factors.iter().all(Value::is_enumerable) || self.emptiness() == Some(true)
                }
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

    /// Whether the set is empty, when that is known without enumerating a set TLC can't.
    fn emptiness(&self) -> Option<bool> {
        let parts = |parts: &mut dyn Iterator<Item = &Value>| {
            for part in parts {
                match part.emptiness() {
                    Some(false) => {}
                    other => return other,
                }
            }
            Some(false)
        };
        match self {
            Value::Set(elements) | Value::MixedSet(elements) => Some(elements.is_empty()),
            Value::Interval(low, high) => Some(low > high),
            Value::Lazy(set) => match &**set {
                LazySet::Any => None,
                LazySet::Nat | LazySet::Int | LazySet::String => Some(false),
                LazySet::Subset(_) | LazySet::Seq(_) => Some(false),
                LazySet::FuncSet { domain, range } => {
                    if domain.emptiness()? {
                        Some(false)
                    } else {
                        range.emptiness()
                    }
                }
                LazySet::RecordSet(fields) => parts(&mut fields.iter().map(|(_, set)| set)),
                LazySet::Product(factors) => parts(&mut factors.iter()),
                LazySet::Cup(..)
                | LazySet::Cap(..)
                | LazySet::Minus(..)
                | LazySet::Filtered { .. }
                | LazySet::Union(_) => self
                    .is_enumerable()
                    .then(|| self.elements().ok().map(|elements| elements.is_empty()))
                    .flatten(),
            },
            _ => None,
        }
    }

    /// The elements in TLC's order.
    pub fn elements(&self) -> Result<Arc<[Value]>> {
        match self {
            Value::Set(elements) => Ok(elements.clone()),
            Value::MixedSet(elements) => Ok(sort_like_tlc(elements)?.into()),
            Value::Interval(low, high) => Ok((*low..=*high).map(Value::Int).collect()),
            Value::Lazy(set) => {
                if let Some(elements) = set.elements().get() {
                    return Ok(elements.clone());
                }
                let elements = self.lazy_elements(set)?;
                Ok(set.elements().get_or_init(|| elements).clone())
            }
            _ => fail!([self], "Expected a set but found {self}"),
        }
    }

    fn lazy_elements(&self, set: &LazySet) -> Result<Arc<[Value]>> {
        match set {
            LazySet::Subset(base) => {
                let subsets = base.subsets()?;
                if subsets.len() > 1 << 30 {
                    fail!([self], "Overflow when computing the number of elements in:\n{self}");
                }
                Ok(subsets.iter().collect())
            }
            LazySet::FuncSet { .. } | LazySet::RecordSet(_) | LazySet::Product(_) => {
                self.combined_elements(set, Value::elements)
            }
            LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => {
                fail!([self], "Attempted to enumerate the non-enumerable set {self}")
            }
            LazySet::Cup(left, right) => {
                if !is_tlc_enumerable(left) || !is_tlc_enumerable(right) {
                    fail!(
                        [left, right],
                        "Attempted to enumerate S \\cup T when S:\n{left}\nand T:\n{right}\nare not both enumerable"
                    );
                }
                let mut elements = left.elements()?.to_vec();
                elements.extend(right.elements()?.iter().cloned());
                Ok(sort_unique(elements)?.into())
            }
            LazySet::Cap(left, right) => {
                let (enumerated, other) = match (is_tlc_enumerable(left), is_tlc_enumerable(right))
                {
                    (true, _) => (left, right),
                    (false, true) => (right, left),
                    (false, false) => fail!(
                        [left, right],
                        "Attempted to enumerate S \\cap T when neither S:\n{left}\nnor T:\n{right}\nis enumerable"
                    ),
                };
                keep(enumerated, |element| other.contains(element))
            }
            LazySet::Minus(left, right) => {
                if !is_tlc_enumerable(left) {
                    fail!(
                        [left],
                        "Attempted to enumerate S \\ T when S:\n{left}\nis not enumerable."
                    );
                }
                keep(left, |element| Ok(!right.contains(element)?))
            }
            LazySet::Filtered { base, test } => {
                if !is_tlc_enumerable(base) {
                    fail!(
                        [base],
                        "Attempted to enumerate {{ x \\in S : p(x) }} when S:\n{base}\nis not enumerable"
                    );
                }
                keep(base, |element| test(element))
            }
            LazySet::Union(base) => {
                let mut elements = Vec::new();
                for (index, set) in union_sets(base, Value::elements)?.iter().enumerate() {
                    elements.extend(union_set(base, set, index)?.elements()?.iter().cloned());
                }
                Value::set(elements)?.elements()
            }
        }
    }

    /// The elements of a set of functions, records, or tuples, built from the elements of the
    /// sets it combines as `elements_of` lists them; the keys of functions in TLC's order.
    pub(crate) fn combined_elements(
        &self,
        set: &LazySet,
        elements_of: ElementsOf,
    ) -> Result<Arc<[Value]>> {
        match self.combinations(set, elements_of)? {
            Some(combinations) => Ok(combinations.iter().collect()),
            None => self.elements(),
        }
    }

    /// The elements of a set of functions, records, or tuples, as `combined_elements` lists them,
    /// to be built as they're read. `None` for any other set.
    pub(crate) fn combinations(
        &self,
        set: &LazySet,
        elements_of: ElementsOf,
    ) -> Result<Option<Combinations>> {
        let combinations = match set {
            LazySet::FuncSet { domain, range } => {
                if self.is_empty()? {
                    return Ok(Some(Combinations::empty()));
                }
                if is_overridden(domain) {
                    fail!(
                        [domain],
                        "Attempted to enumerate a set of the form [D -> R],but the domain D:\n{domain}\ncannot be enumerated."
                    );
                }
                let keys = domain.elements()?;
                if !keys.is_empty() && is_overridden(range) {
                    fail!(
                        [range],
                        "Attempted to enumerate a set of the form [D -> R],but the range R:\n{range}\ncannot be enumerated."
                    );
                }
                let range = if keys.is_empty() { Arc::from([]) } else { elements_of(range)? };
                Combinations::choices(vec![range; keys.len()], Make::Function(keys))
            }
            LazySet::RecordSet(fields) => {
                if self.is_empty()? {
                    return Ok(Some(Combinations::empty()));
                }
                let sets: Vec<&Value> = fields.iter().map(|(_, set)| set).collect();
                let lists = component_elements(&sets, elements_of, |set, index| {
                    format!(
                        "Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `{}' field:\n{set}",
                        fields[index].0
                    )
                })?;
                let names = fields.iter().map(|(name, _)| *name).collect();
                Combinations::choices(lists, Make::Record(names))
            }
            LazySet::Product(factors) => {
                if self.is_empty()? {
                    return Ok(Some(Combinations::empty()));
                }
                let sets: Vec<&Value> = factors.iter().collect();
                let lists = component_elements(&sets, elements_of, |factor, index| {
                    format!(
                        "Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn,\nbut can't enumerate s{index}:\n{factor}"
                    )
                })?;
                Combinations::choices(lists, Make::Tuple)
            }
            _ => return Ok(None),
        };
        Ok(Some(combinations))
    }

    /// The elements of `SUBSET self`: the subsets of this set by size, and then in its order, as
    /// TLC enumerates them.
    pub(crate) fn subsets(&self) -> Result<Combinations> {
        // TLC sizes the base first, and enumerates only the empty set of a base of size 0.
        if self.cardinality()? == 0 {
            return Ok(Combinations::subsets(Arc::from([])));
        }
        if !self.is_set() {
            fail!(
                [self],
                "Attempted to compute the value of an expression of form\nSUBSET S, but S is a non-enumerable value:\n{self}"
            );
        }
        Ok(Combinations::subsets(self.elements()?))
    }

    /// Whether the set is empty, which TLC decides for a set of functions, records, or tuples
    /// from its parts, in order.
    pub fn is_empty(&self) -> Result<bool> {
        match self {
            Value::Set(elements) | Value::MixedSet(elements) => Ok(elements.is_empty()),
            Value::Interval(low, high) => Ok(low > high),
            Value::Lazy(set) => match &**set {
                LazySet::Any => bail!("Shouldn't call isEmpty() on value ANY"),
                LazySet::Nat | LazySet::Int | LazySet::String => Ok(false),
                LazySet::Subset(_) | LazySet::Seq(_) => Ok(false),
                LazySet::Product(factors) => {
                    for factor in factors.iter() {
                        if factor.is_empty()? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                LazySet::RecordSet(fields) => {
                    for (_, set) in fields.iter() {
                        if set.is_empty()? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                LazySet::FuncSet { domain, range } => Ok(!domain.is_empty()? && range.is_empty()?),
                LazySet::Union(base) => {
                    for (index, set) in union_sets(base, Value::elements)?.iter().enumerate() {
                        if !union_set(base, set, index)?.is_empty()? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                _ => Ok(self.elements()?.is_empty()),
            },
            _ => fail!([self], "Shouldn't call isEmpty() on value {self}"),
        }
    }

    /// `value \in self`.
    pub fn contains(&self, value: &Value) -> Result<bool> {
        match self {
            // TLC tests membership in a set enumeration it hasn't normalized member by member,
            // so a comparison that fails fails as the equality of a member with the value. Either
            // way it compares the value with the members as the receiver.
            Value::Set(elements) => {
                value.cache_elements();
                match search(elements, value) {
                    Ok(found) => Ok(found.is_ok()),
                    Err(error) => {
                        for element in elements.iter() {
                            if element.equals(value)? {
                                return Ok(true);
                            }
                        }
                        Err(error)
                    }
                }
            }
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
                _ if low > high => Ok(false),
                _ => fail!(
                    [value, self],
                    "Attempted to check if the value:\n{value}\nis in the integer interval {self}"
                ),
            },
            Value::Lazy(set) => self.lazy_contains(set, value),
            Value::Func(func) if func.keys.iter().all(|key| matches!(key, Value::Str(_))) => {
                fail!(
                    [value, self],
                    "Attempted to check if element:\n{value}\nis in the record:\n{self}"
                )
            }
            Value::Tuple(_) => bail!("Attempted to check set membership in a tuple value."),
            _ => fail!(
                [value, self],
                "Attempted to check if the value:\n{value}\nis an element of the {} {self}",
                describe_kind(self)
            ),
        }
    }

    fn lazy_contains(&self, set: &LazySet, value: &Value) -> Result<bool> {
        let is_model = matches!(value, Value::Model(_));
        match set {
            LazySet::Subset(base) => {
                if !value.is_set() || is_overridden(value) {
                    fail!(
                        [value],
                        "Attempted to check if the non-enumerable value\n{value}\nis element of\n{}",
                        self.printed()?
                    );
                }
                for element in value.elements()?.iter() {
                    if !base.contains(element)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            LazySet::FuncSet { domain, range } => {
                if !value.is_function() {
                    if is_model {
                        return Ok(false);
                    }
                    fail!(
                        [value],
                        "Attempted to check if \n{value}\nwhich is not a TLC function value, is in the set of functions:\n{}",
                        self.printed()?
                    );
                }
                let function = value.materialize()?;
                let (keys, values) = function.entries();
                let is_domain = match interval_low(&keys) {
                    Some(low) => {
                        Value::Interval(low, low + keys.len() as i32 - 1).equals(domain)?
                    }
                    None => domain.equals(&Value::Set(keys.to_vec().into()))?,
                };
                if !is_domain {
                    return Ok(false);
                }
                for item in values.iter() {
                    if !range.contains(item)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            LazySet::RecordSet(fields) => {
                let record = value.is_function().then(|| value.materialize()).transpose()?;
                let Some((keys, values)) = record
                    .as_ref()
                    .map(Value::entries)
                    .filter(|(keys, _)| keys.iter().all(|key| matches!(key, Value::Str(_))))
                else {
                    if is_model {
                        return Ok(false);
                    }
                    fail!(
                        [value],
                        "Attempted to check if non-record\n{value}\nis in the set of records:\n{}",
                        self.printed()?
                    );
                };
                if keys.len() != fields.len() {
                    return Ok(false);
                }
                for (name, set) in fields.iter() {
                    let found =
                        keys.iter().position(|key| matches!(key, Value::Str(key) if key == name));
                    let Some(index) = found else { return Ok(false) };
                    if !set.contains(&values[index])? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            LazySet::Product(factors) => {
                let tuple = value.is_function().then(|| value.materialize()).transpose()?;
                let Some(Value::Tuple(items)) = tuple else {
                    let is_function = tuple.as_ref().is_some_and(|function| {
                        function.entries().0.iter().all(|key| matches!(key, Value::Int(_)))
                    });
                    if is_function || is_model {
                        return Ok(false);
                    }
                    fail!(
                        [value],
                        "Attempted to check if non-tuple\n{value}\nis in the set of tuples:\n{}",
                        self.printed()?
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
            LazySet::Seq(base) => {
                let tuple = value.is_function().then(|| value.materialize()).transpose()?;
                let Some(Value::Tuple(items)) = tuple else {
                    if is_model {
                        return Ok(false);
                    }
                    fail!(
                        [value, self],
                        "Attempted to check if the value:\n{value}\nis an element of {self}."
                    );
                };
                for item in items.iter() {
                    if !base.contains(item)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            LazySet::Any => Ok(true),
            LazySet::Nat | LazySet::Int | LazySet::String => {
                let is_member_type = match set {
                    LazySet::String => matches!(value, Value::Str(_)),
                    _ => matches!(value, Value::Int(_)),
                };
                match value {
                    Value::Model(_) => Ok(false),
                    _ if !is_member_type => {
                        fail!(
                            [value, self],
                            "Attempted to check if the value:\n{value}\nis an element of {self}."
                        )
                    }
                    Value::Int(value) if matches!(set, LazySet::Nat) => Ok(*value >= 0),
                    _ => Ok(true),
                }
            }
            LazySet::Cup(left, right) => Ok(left.contains(value)? || right.contains(value)?),
            LazySet::Cap(left, right) => Ok(left.contains(value)? && right.contains(value)?),
            LazySet::Minus(left, right) => Ok(left.contains(value)? && !right.contains(value)?),
            LazySet::Filtered { base, test } => Ok(base.contains(value)? && test(value)?),
            LazySet::Union(base) => {
                if !is_tlc_enumerable(base) {
                    fail!(
                        [value, base],
                        "Attempted to check if:\n {value}\nis an element of the non-enumerable set:\n UNION({base})"
                    );
                }
                for set in base.elements()?.iter() {
                    if set.contains(value)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
        }
    }

    /// The set as TLC prints it in an error: a small lazy set enumerated, which fails where
    /// enumerating it fails, as TLC's `toString` does.
    fn printed(&self) -> Result<Value> {
        /// TLC prints a set of functions, records, or tuples element by element up to this size.
        const MAXIMUM_EXPANDED_PRODUCT: f64 = 1999.0;
        let product = |sets: &mut dyn Iterator<Item = &Value>| -> Result<f64> {
            let mut size = 1.0;
            for set in sets {
                if size == 0.0 {
                    break;
                }
                size *= f64::from(set.cardinality()?);
            }
            Ok(size)
        };
        let Value::Lazy(set) = self else { return Ok(self.clone()) };
        let is_expanded = match &**set {
            LazySet::Subset(base) => base.cardinality()? <= 6,
            LazySet::FuncSet { domain, range } => {
                if domain.is_enumerable() && domain.cardinality()? == 0 {
                    return Value::set(vec![Value::empty_tuple()]);
                }
                let size = f64::from(range.cardinality()?).powi(domain.cardinality()?);
                size <= MAXIMUM_EXPANDED_PRODUCT
            }
            LazySet::RecordSet(fields) => {
                product(&mut fields.iter().map(|(_, set)| set))? <= MAXIMUM_EXPANDED_PRODUCT
            }
            LazySet::Product(factors) => product(&mut factors.iter())? <= MAXIMUM_EXPANDED_PRODUCT,
            LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => false,
            LazySet::Cup(..)
            | LazySet::Cap(..)
            | LazySet::Minus(..)
            | LazySet::Filtered { .. }
            | LazySet::Union(_) => true,
        };
        if !is_expanded {
            return Ok(self.clone());
        }
        Ok(Value::Set(self.elements()?))
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

    /// `Cardinality(self)`, computed from the parts of a set of functions, records, or tuples
    /// without enumerating it.
    pub fn cardinality(&self) -> Result<i32> {
        let overflow =
            || Error(format!("Overflow when computing the number of elements in:\n{self}"));
        match self {
            Value::Bool(_) | Value::Int(_) | Value::Str(_) => fail!(
                [self],
                "Attempted to compute the number of elements in the {} {self}.",
                describe_kind(self)
            ),
            Value::Model(_) => {
                fail!(
                    [self],
                    "Attempted to compute the number of elements in the model value {self}."
                )
            }
            Value::Tuple(items) => Ok(items.len() as i32),
            Value::Func(func) => Ok(func.keys.len() as i32),
            Value::LazyFunc(lazy) => lazy.domain.cardinality(),
            Value::Interval(low, high) => {
                let size = (i64::from(*high) - i64::from(*low) + 1).max(0);
                i32::try_from(size).map_err(|_| {
                    Error(format!(
                        "Size of interval value exceeds the maximum representable size (32bits): {low}..{high}."
                    ))
                })
            }
            Value::Set(elements) => Ok(elements.len() as i32),
            Value::MixedSet(_) => Ok(self.elements()?.len() as i32),
            Value::Lazy(set) => match &**set {
                LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => {
                    fail!(
                        [self],
                        "Attempted to compute the number of elements in the overridden value {self}."
                    )
                }
                LazySet::Subset(base) => {
                    let size = base.cardinality()?;
                    if size >= 31 {
                        return Err(overflow());
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
                    let range_size = range.cardinality()?;
                    if range_size == 1 {
                        return Ok(1);
                    }
                    let domain_size = domain.cardinality()?;
                    checked_power(i64::from(range_size), i64::from(domain_size), self)
                }
                LazySet::RecordSet(fields) => {
                    if self.is_empty()? {
                        return Ok(0);
                    }
                    let sets: Vec<&Value> = fields.iter().map(|(_, set)| set).collect();
                    product_size(&sets, overflow)
                }
                LazySet::Product(factors) => {
                    if self.is_empty()? {
                        return Ok(0);
                    }
                    product_size(&factors.iter().collect::<Vec<_>>(), || {
                        Error(format!("Overflow when computing the number of elements in {self}"))
                    })
                }
                _ => {
                    self.cache_elements();
                    Ok(self.elements()?.len() as i32)
                }
            },
        }
    }

    /// `self \cup other`.
    pub fn cup(&self, other: &Value) -> Result<Value> {
        self.combine(Operation::Cup, other)
    }

    /// `self \cap other`.
    pub fn cap(&self, other: &Value) -> Result<Value> {
        self.combine(Operation::Cap, other)
    }

    /// `self \ other`.
    pub fn minus(&self, other: &Value) -> Result<Value> {
        self.combine(Operation::Minus, other)
    }

    /// Combines two sets as TLC does: two set enumerations or intervals at once, a set
    /// enumeration or interval with any other set element by element, and other sets lazily. A
    /// non-set operand fails only when the result is used.
    fn combine(&self, operation: Operation, other: &Value) -> Result<Value> {
        let is_sorted = |value: &Value| matches!(value, Value::Set(_) | Value::Interval(..));
        if is_sorted(self) && is_sorted(other) {
            if operation == Operation::Cup && self.is_empty()? {
                return Ok(other.clone());
            }
            if let Ok(merged) = operation.lazy(self, other).elements() {
                return Ok(Value::Set(merged));
            }
            return combine_reducible(operation, self, other);
        }
        if is_reducible(self) {
            return combine_reducible(operation, self, other);
        }
        if operation != Operation::Minus && is_reducible(other) {
            return combine_reducible(operation, other, self);
        }
        Ok(operation.lazy(self, other))
    }

    /// `UNION self`, enumerated when `self` and every set in it are set enumerations, and lazy
    /// otherwise, as TLC builds it.
    pub fn union(&self) -> Result<Value> {
        let lazy = || Value::lazy(LazySet::Union(self.clone()));
        let (Value::Set(sets) | Value::MixedSet(sets)) = self else { return Ok(lazy()) };
        if !sets.iter().all(|set| matches!(set, Value::Set(_) | Value::MixedSet(_))) {
            return Ok(lazy());
        }
        let is_mixed = matches!(self, Value::MixedSet(_))
            || sets.iter().any(|set| matches!(set, Value::MixedSet(_)));
        if !is_mixed {
            let elements = sets.iter().flat_map(|set| set.elements_unchecked()).collect();
            return Ok(Value::Set(sort_unique(elements)?.into()));
        }
        // TLC tests each element for membership in the union so far, element by element.
        let mut members: Vec<Value> = Vec::new();
        for set in sets.iter() {
            for element in set.elements_unchecked() {
                let mut is_member = false;
                for member in &members {
                    if member.equals(&element)? {
                        is_member = true;
                        break;
                    }
                }
                if !is_member {
                    members.push(element);
                }
            }
        }
        Value::set(members)
    }

    /// The elements of a set enumeration as it holds them.
    fn elements_unchecked(&self) -> Vec<Value> {
        match self {
            Value::Set(elements) | Value::MixedSet(elements) => elements.to_vec(),
            _ => Vec::new(),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Operation {
    Cup,
    Cap,
    Minus,
}

impl Operation {
    fn lazy(self, left: &Value, right: &Value) -> Value {
        let (left, right) = (left.clone(), right.clone());
        Value::lazy(match self {
            Operation::Cup => LazySet::Cup(left, right),
            Operation::Cap => LazySet::Cap(left, right),
            Operation::Minus => LazySet::Minus(left, right),
        })
    }
}

/// TLC's `Reducible` sets, a set enumeration or an interval, which combine with another set
/// element by element.
fn is_reducible(value: &Value) -> bool {
    matches!(value, Value::Set(_) | Value::MixedSet(_) | Value::Interval(..))
}

/// Combines a set enumeration or interval with another set by testing each of its elements, in
/// the order the enumeration holds them, for membership in the other set.
fn combine_reducible(operation: Operation, set: &Value, other: &Value) -> Result<Value> {
    let elements = match set {
        Value::Set(elements) | Value::MixedSet(elements) => elements.clone(),
        _ => set.elements()?,
    };
    if operation != Operation::Cup {
        let mut kept = Vec::new();
        for element in elements.iter() {
            if other.contains(element)? == (operation == Operation::Cap) {
                kept.push(element.clone());
            }
        }
        return Value::set(kept);
    }
    if elements.is_empty() {
        return Ok(other.clone());
    }
    if !is_reducible(other) {
        return Ok(operation.lazy(set, other));
    }
    let mut combined = elements.to_vec();
    let others = match other {
        Value::Set(others) | Value::MixedSet(others) => others.clone(),
        _ => other.elements()?,
    };
    for element in others.iter() {
        if !set.contains(element)? {
            combined.push(element.clone());
        }
    }
    Value::set(combined)
}

fn product_size(sets: &[&Value], overflow: impl Fn() -> Error) -> Result<i32> {
    let mut size: i64 = 1;
    for set in sets {
        size = size
            .checked_mul(i64::from(set.cardinality()?))
            .filter(|&size| size <= i64::from(i32::MAX))
            .ok_or_else(&overflow)?;
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
    fn enumerates_a_lazy_set_once() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering};

        let calls = Arc::new(AtomicUsize::new(0));
        let counted = calls.clone();
        let test: crate::Predicate = Arc::new(move |value: &Value| {
            counted.fetch_add(1, Ordering::SeqCst);
            Ok(value.as_int().is_some_and(|value| value % 2 == 0))
        });
        let evens = Value::lazy(LazySet::Filtered { base: Value::Interval(1, 10), test });
        let copy = evens.clone();
        assert_eq!(format(&Value::Set(evens.elements().unwrap())), "{2, 4, 6, 8, 10}");
        assert_eq!(copy.cardinality().unwrap(), 5);
        assert!(evens.equals(&ints(&[2, 4, 6, 8, 10])).unwrap());
        assert_eq!(calls.load(Ordering::SeqCst), 10);
    }

    #[test]
    fn keeps_unsortable_sets_unsorted() {
        let mixed = Value::set(vec![Value::Int(1), Value::str("a")]).unwrap();
        assert!(matches!(mixed, Value::MixedSet(_)));
        assert!(mixed.contains(&Value::Int(1)).unwrap());
        assert!(mixed.elements().is_err());
    }

    fn nat() -> Value {
        Value::lazy(LazySet::Nat)
    }

    fn function_set(domain: Value, range: Value) -> Value {
        Value::lazy(LazySet::FuncSet { domain, range })
    }

    fn message(result: crate::Result<impl std::fmt::Debug>) -> String {
        result.unwrap_err().0
    }

    /// tla-ts's EmptySetEqCases: an empty domain makes a set of functions {<<>>}, and an empty
    /// range, field set, or component makes a set empty, whatever the other parts are.
    #[test]
    fn decides_sets_with_an_empty_part_without_enumerating_the_rest() {
        let unit = function_set(Value::empty_set(), nat());
        assert!(unit.is_enumerable());
        assert_eq!(format(&Value::Set(unit.elements().unwrap())), "{<<>>}");
        assert_eq!(unit.cardinality().unwrap(), 1);
        let unit_set = Value::set(vec![Value::empty_tuple()]).unwrap();
        assert!(unit_set.equals(&unit).unwrap() && unit.equals(&unit_set).unwrap());
        assert!(unit.contains(&Value::empty_tuple()).unwrap());

        let empty = function_set(nat(), Value::empty_set());
        assert!(empty.is_enumerable() && empty.elements().unwrap().is_empty());
        assert_eq!(empty.cardinality().unwrap(), 0);
        let record_set = Value::lazy(LazySet::RecordSet(
            vec![
                (crate::Symbol::intern("n1"), nat()),
                (crate::Symbol::intern("n2"), Value::empty_set()),
            ]
            .into(),
        ));
        assert!(record_set.is_empty().unwrap() && record_set.elements().unwrap().is_empty());
        let product = Value::lazy(LazySet::Product(vec![nat(), Value::empty_set()].into()));
        assert!(Value::empty_set().equals(&product).unwrap());
        assert_eq!(product.cardinality().unwrap(), 0);
    }

    #[test]
    fn refuses_what_tlc_refuses_in_its_words() {
        assert_eq!(
            message(function_set(nat(), ints(&[1])).elements()),
            "Attempted to enumerate a set of the form [D -> R],but the domain D:\nNat\ncannot be enumerated."
        );
        let difference = Value::lazy(LazySet::Minus(nat(), ints(&[0])));
        assert_eq!(
            message(difference.elements()),
            "Attempted to enumerate S \\ T when S:\nNat\nis not enumerable."
        );
        assert_eq!(
            message(nat().cardinality()),
            "Attempted to compute the number of elements in the overridden value Nat."
        );
        assert_eq!(
            message(nat().contains(&Value::str("s"))),
            "Attempted to check if the value:\n\"s\"\nis an element of Nat."
        );
        assert_eq!(message(Value::Int(1).is_empty()), "Shouldn't call isEmpty() on value 1");
        assert_eq!(
            message(Value::str("a").compare(&Value::Int(1))),
            "Attempted to compare string \"a\" with non-string:\n1"
        );
    }

    /// TLC sorts a set enumeration by inserting each element into the sorted prefix, so the
    /// comparison that fails is the one of a later element with an earlier one.
    #[test]
    fn sorts_mixed_sets_as_tlc_does() {
        let mixed = Value::set(vec![Value::Int(1), Value::str("a")]).unwrap();
        assert_eq!(
            message(mixed.elements()),
            "Attempted to compare string \"a\" with non-string:\n1"
        );
    }

    /// tla-ts's ValueSemanticsCases: TLC combines a set enumeration with another set element by
    /// element, putting the enumeration first, and `S \cup {}` is `S`.
    #[test]
    fn combines_sets_as_tlc_does() {
        assert!(nat().cup(&Value::empty_set()).unwrap().equals(&nat()).unwrap());
        assert_eq!(
            message(nat().cup(&ints(&[0])).unwrap().equals(&nat())),
            "Attempted to enumerate S \\cup T when S:\n{0}\nand T:\nNat\nare not both enumerable"
        );
        assert_eq!(format(&nat().cap(&ints(&[-1, 2])).unwrap()), "{2}");
        let mixed = Value::set(vec![Value::Int(1), Value::str("a")]).unwrap();
        assert!(mixed.cup(&Value::empty_set()).unwrap().contains(&Value::Int(1)).unwrap());
        assert!(matches!(
            Value::lazy(LazySet::Subset(ints(&[1]))).minus(&ints(&[1])).unwrap(),
            Value::Lazy(_)
        ));
    }

    /// TLC enumerates `UNION S` at once only when every element of `S` is a set enumeration, so
    /// a set of functions over a large union is sized without enumerating it.
    #[test]
    fn keeps_unions_of_other_sets_lazy() {
        let union = Value::set(vec![
            Value::Interval(1, 2_000_000),
            Value::set(vec![Value::str("a")]).unwrap(),
        ])
        .unwrap()
        .union()
        .unwrap();
        assert!(matches!(union, Value::Lazy(_)));
        assert_eq!(
            function_set(union, Value::set(vec![Value::str("d1")]).unwrap()).cardinality().unwrap(),
            1
        );
        let enumerated = Value::set(vec![ints(&[3, 1]), ints(&[2])]).unwrap().union().unwrap();
        assert_eq!(format(&enumerated), "{1, 2, 3}");
    }

    /// tla-ts's EmptySetEq and Normalization cases: TLC compares a record only with a record,
    /// and tests membership in a set enumeration member by member when a comparison fails.
    #[test]
    fn fails_where_tlc_compares_unlike_values() {
        let record = Value::record(vec![(crate::Symbol::intern("n1"), Value::str("a"))]);
        let pair = Value::tuple(vec![Value::str("a"), Value::str("a")]);
        assert_eq!(
            message(record.equals(&pair)),
            "Attempted to check equality of record:\n[n1 |-> \"a\"]\nwith non-record\n<<\"a\", \"a\">>"
        );
        assert_eq!(
            message(ints(&[1]).contains(&Value::str("a"))),
            "Attempted to check equality of integer 1 with non-integer:\n\"a\""
        );
    }

    /// tla-ts's NormalizationCases: TLC prints a small lazy set in a membership error by
    /// enumerating it, which fails as normalizing a set enumeration it can't sort does.
    #[test]
    fn prints_sets_in_membership_errors_as_tlc_does() {
        let mixed = Value::set(vec![Value::Int(1), Value::str("a")]).unwrap();
        let product = Value::lazy(LazySet::Product(vec![mixed.clone(), Value::empty_set()].into()));
        assert_eq!(
            message(product.contains(&Value::Int(1))),
            "Attempted to compare string \"a\" with non-string:\n1"
        );
        let subsets = Value::lazy(LazySet::Subset(ints(&[1, 2])));
        assert_eq!(
            message(subsets.contains(&Value::Int(1))),
            "Attempted to check if the non-enumerable value\n1\nis element of\n{{}, {1}, {2}, {1, 2}}"
        );
    }
}
