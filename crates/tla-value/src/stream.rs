//! The elements TLC's `Enumerator` streams for `x' \in S` as it generates states. A lazy set
//! streams the sets it combines until TLC caches its elements, so an element two of them share
//! comes up once for each, and a set of tuples, records, or functions over one comes up in the
//! order of its parts.
//!
//! TLC caches a set's elements as the receiver of `compareTo`, `equals`, `size`, and
//! `fingerPrint`, and keeps the cache with the object for as long as it lives. A value here is
//! cached when the same allocation went through one of those, so a set built anew at each
//! evaluation starts out uncached, and one kept between evaluations, such as the value of a
//! constant definition or a variable, stays cached once cached.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError, Weak};

use crate::set::{is_overridden, is_tlc_enumerable, union_set, union_sets};
use crate::{LazySet, Result, Value};

/// Whether a lazy `\cup`, `\cap`, `\`, or `UNION` has been built. Without one, every set streams
/// its elements in TLC's order, so tracking what TLC caches can wait for the first.
static IS_STREAMED: AtomicBool = AtomicBool::new(false);

/// The lazy sets TLC has cached the elements of, by address. Each entry holds a weak reference,
/// which keeps the allocation, and so the address, from being reused while the entry lasts.
static CACHED: Mutex<Cached> = Mutex::new(Cached { sets: BTreeMap::new(), limit: MINIMUM_LIMIT });

struct Cached {
    sets: BTreeMap<usize, Weak<LazySet>>,
    /// The size past which the table drops the sets no longer alive.
    limit: usize,
}

const MINIMUM_LIMIT: usize = 64;

/// Notes a set that can stream apart from its elements in TLC's order.
pub(crate) fn note_lazy(set: &LazySet) {
    if matches!(set, LazySet::Cup(..) | LazySet::Cap(..) | LazySet::Minus(..) | LazySet::Union(_))
        && !IS_STREAMED.load(Ordering::Relaxed)
    {
        IS_STREAMED.store(true, Ordering::Relaxed);
    }
}

/// The sets TLC streams apart from their cached elements: those that combine other sets.
fn is_streaming(set: &LazySet) -> bool {
    matches!(
        set,
        LazySet::Union(_)
            | LazySet::Cup(..)
            | LazySet::Cap(..)
            | LazySet::Minus(..)
            | LazySet::Filtered { .. }
            | LazySet::Product(_)
            | LazySet::RecordSet(_)
            | LazySet::FuncSet { .. }
    )
}

fn cached() -> std::sync::MutexGuard<'static, Cached> {
    CACHED.lock().unwrap_or_else(PoisonError::into_inner)
}

impl Value {
    /// Records that TLC has cached this set's elements, as it does when it compares the set
    /// with another as the receiver, sizes it, or fingerprints it.
    pub fn cache_elements(&self) {
        if !IS_STREAMED.load(Ordering::Relaxed) {
            return;
        }
        let Value::Lazy(set) = self else { return };
        if !is_streaming(set) {
            return;
        }
        let mut cached = cached();
        cached.sets.entry(Arc::as_ptr(set) as usize).or_insert_with(|| Arc::downgrade(set));
        if cached.sets.len() > cached.limit {
            cached.sets.retain(|_, set| set.strong_count() > 0);
            cached.limit = (cached.sets.len() * 2).max(MINIMUM_LIMIT);
        }
    }

    /// Whether TLC has cached this set's elements, after which it enumerates them in its order.
    pub fn has_cached_elements(&self) -> bool {
        if !IS_STREAMED.load(Ordering::Relaxed) {
            return false;
        }
        let Value::Lazy(set) = self else { return false };
        is_streaming(set) && cached().sets.contains_key(&(Arc::as_ptr(set) as usize))
    }

    /// The elements TLC's `Enumerator` yields for `x' \in self`: those of the sets a lazy set
    /// combines, duplicates included, until TLC caches its elements, and those of any other set
    /// in TLC's order.
    pub fn streamed_elements(&self) -> Result<Arc<[Value]>> {
        match self {
            Value::Lazy(set) if IS_STREAMED.load(Ordering::Relaxed) => {
                if self.has_cached_elements() { self.elements() } else { self.stream(set) }
            }
            _ => self.elements(),
        }
    }

    fn stream(&self, set: &LazySet) -> Result<Arc<[Value]>> {
        match set {
            LazySet::Union(base) => {
                let mut elements = Vec::new();
                for (index, set) in union_sets(base, Value::streamed_elements)?.iter().enumerate() {
                    elements
                        .extend(union_set(base, set, index)?.streamed_elements()?.iter().cloned());
                }
                Ok(elements.into())
            }
            LazySet::Filtered { base, test } if !is_overridden(base) => {
                let mut kept = Vec::new();
                for element in base.streamed_elements()?.iter() {
                    if test(element)? {
                        kept.push(element.clone());
                    }
                }
                Ok(kept.into())
            }
            LazySet::FuncSet { range, .. } if range.is_streamed_apart() => {
                self.combined_elements(set, Value::streamed_elements)
            }
            LazySet::RecordSet(fields) if fields.iter().any(|(_, set)| set.is_streamed_apart()) => {
                self.combined_elements(set, Value::streamed_elements)
            }
            LazySet::Product(factors) if factors.iter().any(Value::is_streamed_apart) => {
                self.combined_elements(set, Value::streamed_elements)
            }
            LazySet::Cup(left, right) => {
                if !is_tlc_enumerable(left) || !is_tlc_enumerable(right) {
                    return self.elements();
                }
                let mut elements = left.streamed_elements()?.to_vec();
                elements.extend(right.streamed_elements()?.iter().cloned());
                Ok(elements.into())
            }
            LazySet::Cap(left, right) | LazySet::Minus(left, right) => {
                let is_cap = matches!(set, LazySet::Cap(..));
                let (enumerated, other) =
                    if !is_cap || is_tlc_enumerable(left) { (left, right) } else { (right, left) };
                if !is_tlc_enumerable(enumerated) {
                    return self.elements();
                }
                let mut kept = Vec::new();
                for element in enumerated.streamed_elements()?.iter() {
                    if other.contains(element)? == is_cap {
                        kept.push(element.clone());
                    }
                }
                Ok(kept.into())
            }
            _ => self.elements(),
        }
    }

    /// Whether the set streams its elements in another order than TLC's, so that a set of
    /// tuples, records, or functions it is a part of streams too.
    fn is_streamed_apart(&self) -> bool {
        let Value::Lazy(set) = self else { return false };
        if self.has_cached_elements() {
            return false;
        }
        match &**set {
            LazySet::Union(_) | LazySet::Cup(..) => true,
            LazySet::Filtered { base, .. } => base.is_streamed_apart(),
            LazySet::Cap(left, right) | LazySet::Minus(left, right) => {
                left.is_streamed_apart() || right.is_streamed_apart()
            }
            LazySet::FuncSet { range, .. } => range.is_streamed_apart(),
            LazySet::RecordSet(fields) => fields.iter().any(|(_, set)| set.is_streamed_apart()),
            LazySet::Product(factors) => factors.iter().any(Value::is_streamed_apart),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Value;

    fn ints(values: &[i32]) -> Value {
        Value::set(values.iter().copied().map(Value::Int).collect()).unwrap()
    }

    fn printed(elements: &[Value]) -> Vec<String> {
        elements.iter().map(ToString::to_string).collect()
    }

    /// `UNION {{3, 1}, 0..1}`, lazy for the interval in it.
    fn union() -> Value {
        Value::set(vec![ints(&[3, 1]), Value::Interval(0, 1)]).unwrap().union().unwrap()
    }

    #[test]
    fn streams_the_sets_a_union_combines_until_cached() {
        let set = union();
        assert!(matches!(set, Value::Lazy(_)));
        assert_eq!(printed(&set.streamed_elements().unwrap()), ["0", "1", "1", "3"]);
        assert!(!set.has_cached_elements());
        assert_eq!(set.cardinality().unwrap(), 3);
        assert!(set.has_cached_elements());
        assert_eq!(printed(&set.streamed_elements().unwrap()), ["0", "1", "3"]);
        // A union built anew starts out uncached.
        assert_eq!(union().streamed_elements().unwrap().len(), 4);
    }

    #[test]
    fn streams_a_cup_operand_by_operand() {
        let left = Value::set(vec![ints(&[1]), ints(&[2])]).unwrap().union().unwrap();
        let cup = Value::lazy(crate::LazySet::Cup(Value::Interval(2, 3), left));
        assert_eq!(printed(&cup.streamed_elements().unwrap()), ["2", "3", "1", "2"]);
        assert_eq!(printed(&cup.elements().unwrap()), ["1", "2", "3"]);
        // TLC caches the receiver of an equality, not its argument.
        assert!(union().equals(&cup).is_ok());
        assert!(!cup.has_cached_elements());
        assert!(cup.equals(&union()).is_ok());
        assert!(cup.has_cached_elements());
    }

    #[test]
    fn streams_the_records_over_a_streamed_part() {
        let fields = vec![
            (crate::Symbol::intern("a"), Value::Interval(1, 2)),
            (crate::Symbol::intern("b"), union()),
        ];
        let records = Value::lazy(crate::LazySet::RecordSet(fields.into()));
        let streamed = records.streamed_elements().unwrap();
        assert_eq!(streamed.len(), 8);
        assert_eq!(streamed[0].to_string(), "[a |-> 1, b |-> 0]");
        assert_eq!(records.elements().unwrap().len(), 6);
    }

    #[test]
    fn caches_an_element_tested_against_a_set_enumeration_and_a_fingerprinted_set() {
        let set = union();
        assert!(!Value::set(vec![ints(&[1])]).unwrap().contains(&set).unwrap());
        assert!(set.has_cached_elements());
        let set = union();
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        set.fingerprint(&mut hasher).unwrap();
        assert!(set.has_cached_elements());
        let set = union();
        Value::set(vec![ints(&[1]), set.clone()]).unwrap();
        assert!(set.has_cached_elements());
    }
}
