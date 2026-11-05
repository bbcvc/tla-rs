//! The elements of a set of functions, records, or tuples, or of a power set, built one at a time
//! from the elements of the sets it combines, in TLC's order, so that a loop that stops early,
//! such as `CHOOSE` or a quantifier that finds its witness, never builds the rest.

use std::sync::{Arc, Mutex, PoisonError};

use crate::{LazySet, Result, Symbol, Value};

/// The elements of a set in TLC's order, as [`Value::enumeration`] lists them.
#[derive(Clone)]
pub enum Enumeration {
    /// `low..high`, kept as an interval, so that a quantifier can stop at its first witness in a
    /// large one without listing it, as TLC does.
    Interval(i32, i32),
    List(Arc<[Value]>),
    /// The elements of a large set of functions, records, or tuples, or of a large power set,
    /// built as they're read.
    Combined(Arc<Combinations>),
}

impl Enumeration {
    pub fn len(&self) -> usize {
        match self {
            Enumeration::Interval(low, high) => {
                (i64::from(*high) - i64::from(*low) + 1).max(0) as usize
            }
            Enumeration::List(elements) => elements.len(),
            Enumeration::Combined(combinations) => combinations.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The element at `index`, which is less than [`Enumeration::len`].
    pub fn get(&self, index: usize) -> Value {
        match self {
            Enumeration::Interval(low, _) => Value::Int(low + index as i32),
            Enumeration::List(elements) => elements[index].clone(),
            Enumeration::Combined(combinations) => combinations.get(index),
        }
    }

    /// The elements in order.
    pub fn iter(&self) -> impl Iterator<Item = Value> + '_ {
        (0..self.len()).map(|index| self.get(index))
    }
}

/// Past this many elements, a set of functions, records, or tuples, or a power set, builds its
/// elements as they're read rather than all at once, and doesn't keep them.
const BUILT_AT_ONCE: usize = 1 << 16;

impl Value {
    /// The elements in TLC's order, as [`Value::elements`] lists them, except that an interval
    /// stays an interval, and the elements of a large set of functions, records, or tuples, or
    /// of a large power set, are built one at a time as they're read. A power set of more than
    /// 30 elements, too large to list, is enumerated this way, as TLC enumerates it.
    pub fn enumeration(&self) -> Result<Enumeration> {
        self.enumeration_past(BUILT_AT_ONCE)
    }

    /// [`Value::enumeration`], building the elements as they're read past `limit` of them.
    pub(crate) fn enumeration_past(&self, limit: usize) -> Result<Enumeration> {
        let set = match self {
            Value::Interval(low, high) => return Ok(Enumeration::Interval(*low, *high)),
            Value::Lazy(set) if set.elements().get().is_none() => set,
            _ => return Ok(Enumeration::List(self.elements()?)),
        };
        let combinations = match &**set {
            LazySet::Subset(base) => base.subsets()?,
            _ => match self.combinations(set, Value::elements)? {
                Some(combinations) => combinations,
                None => return Ok(Enumeration::List(self.elements()?)),
            },
        };
        if combinations.len() > limit {
            return Ok(Enumeration::Combined(Arc::new(combinations)));
        }
        let elements = combinations.iter().collect();
        Ok(Enumeration::List(set.elements().get_or_init(|| elements).clone()))
    }
}

/// Every choice of one element from each of some lists, the first list varying slowest, made into
/// a function, record, or tuple; or every subset of a base, by size and then in the order of the
/// base. Either is TLC's order when the lists or the base are in TLC's order.
pub struct Combinations {
    shape: Shape,
    /// The number of elements, or `usize::MAX` for more.
    len: usize,
}

enum Shape {
    Choices {
        lists: Box<[Arc<[Value]>]>,
        make: Make,
    },
    Subsets {
        base: Arc<[Value]>,
        /// The last subset built, by its index and the indexes of its elements in the base, from
        /// which the next is a step away.
        last: Mutex<Option<(usize, Vec<usize>)>>,
    },
}

/// What a choice of one element from each list makes.
pub(crate) enum Make {
    /// The function from each key, sorted and distinct, to the element chosen for it.
    Function(Arc<[Value]>),
    /// The record with the element chosen for each field.
    Record(Box<[Symbol]>),
    Tuple,
}

impl Combinations {
    /// Every choice of one element from each of `lists`, made into a value by `make`.
    pub(crate) fn choices(lists: Vec<Arc<[Value]>>, make: Make) -> Self {
        let len = if lists.iter().any(|list| list.is_empty()) {
            0
        } else {
            lists
                .iter()
                .try_fold(1, |len: usize, list| len.checked_mul(list.len()))
                .unwrap_or(usize::MAX)
        };
        Self { shape: Shape::Choices { lists: lists.into(), make }, len }
    }

    /// No elements.
    pub(crate) fn empty() -> Self {
        Self::choices(vec![Arc::from([])], Make::Tuple)
    }

    /// Every subset of `base`, which is sorted.
    pub(crate) fn subsets(base: Arc<[Value]>) -> Self {
        let len = u32::try_from(base.len())
            .ok()
            .and_then(|size| 1usize.checked_shl(size))
            .unwrap_or(usize::MAX);
        Self { shape: Shape::Subsets { base, last: Mutex::new(None) }, len }
    }

    /// The number of elements, or `usize::MAX` for more.
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The element at `index`, which is less than [`Combinations::len`].
    pub fn get(&self, index: usize) -> Value {
        debug_assert!(index < self.len, "index {index} of {} combinations", self.len);
        match &self.shape {
            Shape::Choices { lists, make } => {
                let mut rest = index;
                let mut chosen: Vec<Value> = lists
                    .iter()
                    .rev()
                    .map(|list| {
                        let item = list[rest % list.len()].clone();
                        rest /= list.len();
                        item
                    })
                    .collect();
                chosen.reverse();
                make.make(chosen)
            }
            Shape::Subsets { base, last } => {
                let mut last = last.lock().unwrap_or_else(PoisonError::into_inner);
                let is_found = match &mut *last {
                    Some((at, _)) if *at == index => true,
                    Some((at, indexes)) if *at + 1 == index => {
                        *at = index;
                        next_subset(indexes, base.len())
                    }
                    _ => false,
                };
                let (_, indexes) = match &mut *last {
                    Some(last) if is_found => last,
                    last => last.insert((index, subset_at(base.len(), index))),
                };
                Value::Set(indexes.iter().map(|&item| base[item].clone()).collect())
            }
        }
    }

    /// The elements in order.
    pub fn iter(&self) -> impl Iterator<Item = Value> + '_ {
        (0..self.len).map(|index| self.get(index))
    }
}

impl Make {
    fn make(&self, chosen: Vec<Value>) -> Value {
        match self {
            Make::Function(keys) => Value::from_sorted(keys.to_vec(), chosen),
            Make::Record(names) => Value::record(names.iter().copied().zip(chosen).collect()),
            Make::Tuple => Value::tuple(chosen),
        }
    }
}

/// Steps the indexes of a subset of a base of `size` elements to those of the next subset: the
/// next of the same size in the order of the base, or the first of the next size. Returns whether
/// there is one.
fn next_subset(indexes: &mut Vec<usize>, size: usize) -> bool {
    let count = indexes.len();
    match (0..count).rev().find(|&position| indexes[position] < size - count + position) {
        Some(position) => {
            indexes[position] += 1;
            for next in position + 1..count {
                indexes[next] = indexes[next - 1] + 1;
            }
            true
        }
        None if count < size => {
            indexes.clear();
            indexes.extend(0..=count);
            true
        }
        None => false,
    }
}

/// The indexes in the base of the subset at `index` of the subsets of a base of `size` elements,
/// by size and then in the order of the base.
fn subset_at(size: usize, mut index: usize) -> Vec<usize> {
    let mut count = 0;
    loop {
        let subsets = binomial(size, count);
        if index < subsets {
            break;
        }
        index -= subsets;
        count += 1;
    }
    let mut indexes = Vec::with_capacity(count);
    let mut item = 0;
    for position in 0..count {
        // The subsets whose element at `position` is `item` come before those with a later one.
        loop {
            let with_item = binomial(size - item - 1, count - position - 1);
            if index < with_item {
                break;
            }
            index -= with_item;
            item += 1;
        }
        indexes.push(item);
        item += 1;
    }
    indexes
}

/// The number of ways to choose `k` of `n` things, or `usize::MAX` for more. A saturated count
/// still decides `index < count` for every index below `usize::MAX`.
fn binomial(n: usize, k: usize) -> usize {
    if k > n {
        return 0;
    }
    let k = k.min(n - k);
    let mut result: u128 = 1;
    for step in 0..k {
        // Now the number of ways to choose `step + 1` of `n`, which grows with `step` up to `k`.
        result = result * (n - step) as u128 / (step + 1) as u128;
        if result >= usize::MAX as u128 {
            return usize::MAX;
        }
    }
    result as usize
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ints(values: &[i32]) -> Arc<[Value]> {
        values.iter().copied().map(Value::Int).collect()
    }

    fn printed(combinations: &Combinations) -> Vec<String> {
        combinations.iter().map(|value| value.to_string()).collect()
    }

    #[test]
    fn chooses_with_the_first_list_varying_slowest() {
        let tuples = Combinations::choices(vec![ints(&[1, 2]), ints(&[3, 4, 5])], Make::Tuple);
        assert_eq!(tuples.len(), 6);
        assert_eq!(
            printed(&tuples),
            ["<<1, 3>>", "<<1, 4>>", "<<1, 5>>", "<<2, 3>>", "<<2, 4>>", "<<2, 5>>"]
        );
        assert_eq!(tuples.get(4).to_string(), "<<2, 4>>");
        assert!(Combinations::choices(vec![ints(&[1]), ints(&[])], Make::Tuple).is_empty());
        assert_eq!(printed(&Combinations::choices(Vec::new(), Make::Tuple)), ["<<>>"]);
    }

    #[test]
    fn counts_past_the_largest_index() {
        let many = Combinations::choices(vec![ints(&[1, 2, 3, 4]); 40], Make::Tuple);
        assert_eq!(many.len(), usize::MAX);
        let mut empty = vec![ints(&[1, 2, 3, 4]); 40];
        empty.push(ints(&[]));
        assert_eq!(Combinations::choices(empty, Make::Tuple).len(), 0);
        assert_eq!(Combinations::subsets(ints(&[0; 64])).len(), usize::MAX);
        assert_eq!(Combinations::subsets(ints(&[0; 63])).len(), 1 << 63);
    }

    #[test]
    fn lists_subsets_by_size_then_in_the_order_of_the_base() {
        let subsets = Combinations::subsets(ints(&[1, 2, 3]));
        assert_eq!(
            printed(&subsets),
            ["{}", "{1}", "{2}", "{3}", "{1, 2}", "{1, 3}", "{2, 3}", "{1, 2, 3}"]
        );
        assert_eq!(printed(&Combinations::subsets(ints(&[]))), ["{}"]);
    }

    /// Reading the subsets out of order finds each where reading them in order does.
    #[test]
    fn finds_any_subset_by_its_index() {
        let base: Vec<i32> = (1..=9).collect();
        let in_order = printed(&Combinations::subsets(ints(&base)));
        let subsets = Combinations::subsets(ints(&base));
        for index in (0..in_order.len()).rev().step_by(7).chain([0, 511, 3, 4, 4, 5]) {
            assert_eq!(subsets.get(index).to_string(), in_order[index], "subset {index}");
        }
    }

    #[test]
    fn finds_subsets_of_bases_too_large_to_count() {
        let base: Vec<i32> = (1..=100).collect();
        let subsets = Combinations::subsets(ints(&base));
        assert_eq!(subsets.get(0).to_string(), "{}");
        assert_eq!(subsets.get(100).to_string(), "{100}");
        assert_eq!(subsets.get(101).to_string(), "{1, 2}");
        // After the empty set, the 100 singletons, and the 4950 pairs.
        assert_eq!(subsets.get(5051).to_string(), "{1, 2, 3}");
        assert!(subsets.get(usize::MAX - 1).cardinality().unwrap() > 3);
    }

    fn set(values: Vec<Value>) -> Value {
        Value::set(values).unwrap()
    }

    fn lazy(set: LazySet) -> Value {
        Value::lazy(set)
    }

    fn strs(texts: &[&str]) -> Value {
        set(texts.iter().map(|text| Value::str(text)).collect())
    }

    /// Sets of functions, records, and tuples, and power sets, built anew at each call, so that
    /// none keeps the elements another enumerated.
    fn combined_sets() -> Vec<Value> {
        let interval = |low, high| Value::Interval(low, high);
        let mut fields =
            vec![(Symbol::intern("b"), interval(1, 3)), (Symbol::intern("a"), strs(&["x", "y"]))];
        fields.sort_by_key(|(name, _)| *name);
        vec![
            lazy(LazySet::FuncSet { domain: interval(1, 3), range: interval(1, 4) }),
            lazy(LazySet::FuncSet { domain: strs(&["p", "q"]), range: interval(1, 3) }),
            lazy(LazySet::FuncSet { domain: Value::empty_set(), range: interval(1, 3) }),
            lazy(LazySet::FuncSet { domain: interval(1, 2), range: Value::empty_set() }),
            lazy(LazySet::FuncSet {
                domain: interval(1, 2),
                range: lazy(LazySet::Subset(set(vec![Value::Int(1), Value::Int(2)]))),
            }),
            lazy(LazySet::RecordSet(fields.into())),
            lazy(LazySet::Product(vec![interval(1, 3), strs(&["b", "a"]), interval(0, 1)].into())),
            lazy(LazySet::Product(vec![interval(1, 3), Value::empty_set()].into())),
            lazy(LazySet::Product(
                vec![
                    lazy(LazySet::Product(vec![interval(1, 2), interval(1, 2)].into())),
                    strs(&["z"]),
                ]
                .into(),
            )),
            lazy(LazySet::Subset(interval(1, 5))),
            lazy(LazySet::Subset(Value::empty_set())),
            lazy(LazySet::Subset(lazy(LazySet::Product(
                vec![interval(1, 2), interval(1, 2)].into(),
            )))),
        ]
    }

    fn printed_all(values: impl Iterator<Item = Value>) -> Vec<String> {
        values.map(|value| value.to_string()).collect()
    }

    /// Built one at a time, the elements are those `elements` lists, in its order.
    #[test]
    fn enumerates_the_elements_in_tlc_order() {
        for (set, fresh) in combined_sets().into_iter().zip(combined_sets()) {
            let enumeration = fresh.enumeration_past(0).unwrap();
            let is_combined = matches!(enumeration, Enumeration::Combined(_));
            assert!(is_combined || enumeration.is_empty(), "{set}");
            let elements = set.elements().unwrap();
            assert_eq!(enumeration.len(), elements.len(), "{set}");
            assert_eq!(
                printed_all(enumeration.iter()),
                printed_all(elements.iter().cloned()),
                "{set}"
            );
            let sorted = printed_all(
                Value::set(elements.to_vec()).unwrap().elements().unwrap().iter().cloned(),
            );
            assert_eq!(printed_all(elements.iter().cloned()), sorted, "{set}");
            for index in (0..enumeration.len()).rev() {
                assert_eq!(
                    enumeration.get(index).to_string(),
                    elements[index].to_string(),
                    "{set}"
                );
            }
        }
    }

    /// A small set lists its elements once and keeps them, as `elements` does.
    #[test]
    fn keeps_the_elements_of_small_sets() {
        for set in combined_sets() {
            let Enumeration::List(listed) = set.enumeration().unwrap() else {
                panic!("{set} isn't listed")
            };
            assert!(Arc::ptr_eq(&listed, &set.elements().unwrap()), "{set}");
        }
        let large =
            lazy(LazySet::FuncSet { domain: Value::Interval(1, 9), range: Value::Interval(1, 4) });
        assert!(matches!(large.enumeration().unwrap(), Enumeration::Combined(_)));
        assert!(matches!(
            Value::Interval(1, 9).enumeration().unwrap(),
            Enumeration::Interval(1, 9)
        ));
    }

    /// The enumeration fails as `elements` does on a set it can't enumerate.
    #[test]
    fn fails_as_listing_the_elements_fails() {
        let failing = || {
            vec![
                lazy(LazySet::FuncSet { domain: Value::Interval(1, 2), range: lazy(LazySet::Nat) }),
                lazy(LazySet::FuncSet { domain: lazy(LazySet::Nat), range: Value::Interval(1, 2) }),
                lazy(LazySet::Product(vec![Value::Interval(1, 2), lazy(LazySet::Int)].into())),
                lazy(LazySet::Subset(lazy(LazySet::Nat))),
                lazy(LazySet::Subset(Value::Int(3))),
            ]
        };
        for (set, fresh) in failing().into_iter().zip(failing()) {
            let listed = set.elements().err().map(|error| error.0);
            let enumerated = fresh.enumeration_past(0).err().map(|error| error.0);
            assert!(listed.is_some(), "{set}");
            assert_eq!(listed, enumerated, "{set}");
        }
    }

    /// TLC enumerates a power set too large to list one subset at a time.
    #[test]
    fn enumerates_power_sets_too_large_to_list() {
        let set = lazy(LazySet::Subset(Value::Interval(1, 40)));
        assert!(set.elements().unwrap_err().0.starts_with("Overflow when computing"));
        let enumeration = set.enumeration().unwrap();
        assert_eq!(enumeration.len(), 1 << 40);
        assert_eq!(enumeration.get(41).to_string(), "{1, 2}");
    }

    #[test]
    fn counts_choices() {
        assert_eq!(binomial(5, 2), 10);
        assert_eq!(binomial(5, 0), 1);
        assert_eq!(binomial(5, 6), 0);
        assert_eq!(binomial(62, 31), 465428353255261088);
        assert_eq!(binomial(200, 100), usize::MAX);
    }
}
