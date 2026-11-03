//! TLC's random choices, ported from tla-ts `tlc/random.ts`: `java.util.Random`, which TLC's
//! `RandomEnumerableValues` extends, `RandomElement`, and the subset enumeration behind
//! `Randomization!RandomSubset`.

use std::sync::OnceLock;

use tla_value::{LazySet, Result, Value};

const MULTIPLIER: u64 = 0x5_deec_e66d;
const ADDEND: u64 = 0xb;
const SEED_MASK: u64 = (1 << 48) - 1;

/// `java.util.Random`, a 48-bit linear congruential generator.
#[derive(Clone, Copy, Debug)]
pub(crate) struct JavaRandom {
    state: u64,
}

impl JavaRandom {
    pub fn new(seed: i64) -> Self {
        Self { state: (seed as u64 ^ MULTIPLIER) & SEED_MASK }
    }

    fn next(&mut self, bits: u32) -> i32 {
        self.state = self.state.wrapping_mul(MULTIPLIER).wrapping_add(ADDEND) & SEED_MASK;
        (self.state >> (48 - bits)) as u32 as i32
    }

    /// A number in `0..bound`, for a positive `bound`.
    pub fn next_int(&mut self, bound: i32) -> i32 {
        let first = self.next(31);
        let mask = bound - 1;
        if bound & mask == 0 {
            return ((i64::from(bound) * i64::from(first)) >> 31) as i32;
        }
        let mut candidate = first;
        loop {
            let value = candidate % bound;
            if i64::from(candidate) - i64::from(value) + i64::from(mask) <= i64::from(i32::MAX) {
                return value;
            }
            candidate = self.next(31);
        }
    }

    pub fn next_long(&mut self) -> i64 {
        let high = i64::from(self.next(32));
        (high << 32).wrapping_add(i64::from(self.next(32)))
    }

    pub fn next_double(&mut self) -> f64 {
        let high = i64::from(self.next(26));
        ((high << 27) + i64::from(self.next(27))) as f64 * (1.0 / (1u64 << 53) as f64)
    }
}

fn empty_set_error() -> tla_value::Error {
    tla_value::Error("RandomElement of the empty set".to_owned())
}

/// `TLC!RandomElement`, which chooses each component of a set of functions, records, or tuples
/// separately, and otherwise indexes the enumerated set with `nextDouble`.
pub(crate) fn random_element(set: &Value, random: &mut JavaRandom) -> Result<Value> {
    if let Value::Lazy(lazy) = set {
        match &**lazy {
            LazySet::FuncSet { domain, range } => {
                let keys = domain.elements()?;
                let mut pairs = Vec::with_capacity(keys.len());
                for key in keys.iter() {
                    pairs.push((key.clone(), random_element(range, random)?));
                }
                return Value::function(pairs);
            }
            LazySet::RecordSet(fields) => {
                let mut record = Vec::with_capacity(fields.len());
                for (name, set) in fields.iter() {
                    record.push((*name, random_element(set, random)?));
                }
                return Ok(Value::record(record));
            }
            LazySet::Product(factors) => {
                let items = factors.iter().map(|factor| random_element(factor, random));
                return Ok(Value::tuple(items.collect::<Result<_>>()?));
            }
            _ => {}
        }
    }
    if let Value::Interval(low, high) = set {
        let size = (i64::from(*high) - i64::from(*low) + 1).max(0);
        let offset = (random.next_double() * size as f64).floor() as i64;
        if offset >= size {
            return Err(empty_set_error());
        }
        return Ok(Value::Int((i64::from(*low) + offset) as i32));
    }
    let elements = set.elements()?;
    let index = (random.next_double() * elements.len() as f64).floor() as usize;
    elements.get(index).cloned().ok_or_else(empty_set_error)
}

/// `RandomGenerator.primes`: the 1341 consecutive primes from 1277011 to 1295953.
fn primes() -> &'static [u64] {
    static PRIMES: OnceLock<Vec<u64>> = OnceLock::new();
    PRIMES.get_or_init(|| {
        let is_prime = |candidate: u64| {
            (2..).take_while(|d| d * d <= candidate).all(|d| !candidate.is_multiple_of(d))
        };
        (1_277_011..).filter(|&candidate| is_prime(candidate)).take(1341).collect()
    })
}

fn next_prime(random: &mut JavaRandom) -> u64 {
    let primes = primes();
    let mut index = primes.len();
    while index == primes.len() {
        index = (random.next_double() * primes.len() as f64).floor() as usize;
    }
    primes[index]
}

fn prime_factors(mut value: u64) -> Vec<u64> {
    let mut factors = Vec::new();
    let mut divisor = 2;
    while divisor * divisor <= value {
        while value.is_multiple_of(divisor) {
            factors.push(divisor);
            value /= divisor;
        }
        divisor += 1;
    }
    if value > 1 {
        factors.push(value);
    }
    factors
}

/// EnumerableValue.computeOptimalMandA: the smallest modulus at least `max(size, 9)` that isn't a
/// multiple of 4 and has a repeated prime factor, and 1 plus the product of its distinct prime
/// factors.
fn modulus_and_multiplier(size: u64) -> (u64, u64) {
    let mut modulus = size.max(9);
    loop {
        let factors = prime_factors(modulus);
        let mut distinct = factors.clone();
        distinct.dedup();
        if !modulus.is_multiple_of(4) && distinct.len() != factors.len() {
            return (modulus, distinct.iter().product::<u64>() + 1);
        }
        modulus += 1;
    }
}

/// EnumerableValue.SubsetEnumerator: `count` indices below `size` from a full-period linear
/// congruential generator that starts at `random.nextInt(size)`.
fn subset_indices(count: i32, size: u64, random: &mut JavaRandom) -> Vec<u128> {
    if size == 0 {
        return Vec::new();
    }
    let (modulus, multiplier) = modulus_and_multiplier(size);
    let mut index = random.next_int(size as i32) as u64;
    let increment = next_prime(random);
    (0..count)
        .map(|_| {
            loop {
                index = (multiplier * index + increment) % modulus;
                if index < size {
                    break;
                }
            }
            u128::from(index)
        })
        .collect()
}

const LARGE_STRIDE: i128 = i64::MAX as i128 - 24;

/// SetOfFcnsOrRcdsValue.BigIntegerSubsetEnumerator, for products of more than 2^31 - 1
/// elements. `size` is `None` when it exceeds even 128 bits.
fn large_subset_indices(count: i32, size: Option<u128>, random: &mut JavaRandom) -> Vec<u128> {
    let offset = random.next_long().wrapping_abs();
    (0..count)
        .map(|index| {
            let value = LARGE_STRIDE * i128::from(index) + i128::from(offset);
            match size {
                Some(size) => value.rem_euclid(size as i128) as u128,
                None => value.unsigned_abs(),
            }
        })
        .collect()
}

/// The element of a product at `index`, the last factor varying fastest.
fn product_element(lists: &[std::sync::Arc<[Value]>], mut index: u128) -> Vec<Value> {
    let mut elements = vec![Value::FALSE; lists.len()];
    for (position, list) in lists.iter().enumerate().rev() {
        let length = list.len() as u128;
        elements[position] = list[(index % length) as usize].clone();
        index /= length;
    }
    elements
}

/// Enumerable#getRandomSubset: up to `count` elements of `set`, chosen as TLC chooses them.
pub(crate) fn random_subset(
    count: i32,
    set: &Value,
    random: &mut JavaRandom,
) -> Result<Vec<Value>> {
    if set.is_empty()? {
        return Ok(Vec::new());
    }
    if let Value::Interval(low, high) = set {
        let size = (i64::from(*high) - i64::from(*low) + 1) as u64;
        let indices = subset_indices(count, size, random);
        return Ok(indices.into_iter().map(|index| Value::Int(*low + index as i32)).collect());
    }
    let product = match set {
        Value::Lazy(lazy) => match &**lazy {
            LazySet::FuncSet { domain, range } => {
                let keys = domain.elements()?;
                Some((vec![range.elements()?; keys.len()], Some(keys), None))
            }
            LazySet::RecordSet(fields) => {
                let lists = fields.iter().map(|(_, set)| set.elements()).collect::<Result<_>>()?;
                Some((lists, None, Some(fields.iter().map(|(name, _)| *name).collect::<Vec<_>>())))
            }
            LazySet::Product(factors) => {
                Some((factors.iter().map(Value::elements).collect::<Result<_>>()?, None, None))
            }
            _ => None,
        },
        _ => None,
    };
    let Some((lists, keys, names)) = product else {
        let elements = set.elements()?;
        let indices = subset_indices(count, elements.len() as u64, random);
        return Ok(indices.into_iter().map(|index| elements[index as usize].clone()).collect());
    };
    let size = lists.iter().try_fold(1u128, |size, list| size.checked_mul(list.len() as u128));
    let indices = match size {
        Some(size) if size <= i32::MAX as u128 => subset_indices(count, size as u64, random),
        _ => large_subset_indices(count, size, random),
    };
    indices
        .into_iter()
        .map(|index| {
            let elements = product_element(&lists, index);
            if let Some(keys) = &keys {
                Value::function(keys.iter().cloned().zip(elements).collect())
            } else if let Some(names) = &names {
                Ok(Value::record(names.iter().copied().zip(elements).collect()))
            } else {
                Ok(Value::tuple(elements))
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use tla_value::{LazySet, Symbol, Value};

    use super::{JavaRandom, primes, random_element, random_subset};
    use crate::stdlib::testing::ints;

    #[test]
    fn matches_java_util_random() {
        let mut random = JavaRandom::new(0);
        assert_eq!(random.next_int(i32::MAX), 1569741360);
        assert_eq!(random.next_double(), 0.8314409887870612);
        assert_eq!(random.next_long(), -7261648964369397258);
        assert_eq!(random.next_int(10), 3);
        assert_eq!(random.next_int(16), 8);
        let mut random = JavaRandom::new(42);
        assert_eq!((random.next_int(10), random.next_int(100)), (0, 63));
        assert_eq!(random.next_double(), 0.6832234717598454);
        let mut random = JavaRandom::new(-2252017213236477395);
        assert_eq!(random.next_double(), 0.9778076430313554);
        assert_eq!(random.next_int(7), 0);
        assert_eq!(random.next_long(), 1340707523492279093);
    }

    fn texts(values: &[Value]) -> String {
        values.iter().map(Value::to_string).collect::<Vec<_>>().join(" ")
    }

    fn lazy(set: LazySet) -> Value {
        Value::lazy(set)
    }

    #[test]
    fn chooses_elements_like_tla_ts() {
        let mut random = JavaRandom::new(1);
        let mut choose = |set: &Value| random_element(set, &mut random).unwrap();
        let interval = Value::Interval(1, 1000);
        assert_eq!(texts(&[0; 5].map(|_| choose(&interval))), "731 411 208 333 968");
        let set = ints(&[5, 7, 9, 11]);
        assert_eq!(texts(&[0; 3].map(|_| choose(&set))), "5 11 11");
        let functions =
            lazy(LazySet::FuncSet { domain: Value::Interval(1, 3), range: ints(&[0, 1]) });
        assert_eq!(choose(&functions).to_string(), "<<1, 1, 0>>");
        let booleans = Value::set(vec![Value::TRUE, Value::FALSE]).unwrap();
        let product = lazy(LazySet::Product(vec![Value::Interval(1, 9), booleans].into()));
        assert_eq!(choose(&product).to_string(), "<<4, FALSE>>");
        let records =
            lazy(LazySet::RecordSet(vec![(Symbol::intern("a"), Value::empty_set())].into()));
        assert_eq!(
            random_element(&records, &mut JavaRandom::new(1)).unwrap_err().0,
            "RandomElement of the empty set"
        );
    }

    #[test]
    fn chooses_subsets_like_tla_ts() {
        let mut random = JavaRandom::new(15041980);
        let mut subset =
            |count: i32, set: &Value| texts(&random_subset(count, set, &mut random).unwrap());
        assert_eq!(subset(5, &Value::Interval(1, 100)), "6 41 37 29 25");
        assert_eq!(subset(3, &Value::Interval(-5, 1000000)), "603616 895416 853877");
        assert_eq!(subset(3, &ints(&[2, 4, 6, 8, 10, 12, 14])), "8 4 6");
        assert_eq!(subset(10, &ints(&[2, 4, 6])), "4 6 2 4 6 2 4 6 2 4");
        let functions =
            lazy(LazySet::FuncSet { domain: Value::Interval(1, 3), range: Value::Interval(0, 4) });
        assert_eq!(subset(4, &functions), "<<2, 0, 2>> <<2, 0, 1>> <<1, 4, 0>> <<0, 1, 4>>");
        let product =
            lazy(LazySet::Product(vec![Value::Interval(1, 9), Value::Interval(0, 2)].into()));
        assert_eq!(subset(3, &product), "<<7, 0>> <<3, 1>> <<6, 2>>");
        let large = lazy(LazySet::FuncSet {
            domain: Value::Interval(1, 10),
            range: Value::Interval(1, 100),
        });
        assert_eq!(
            subset(3, &large),
            "<<1, 68, 23, 40, 98, 72, 79, 35, 45, 88>> <<10, 90, 57, 13, 2, 41, 34, 13, 3, 71>> <<20, 12, 90, 85, 6, 9, 88, 90, 61, 54>>"
        );
        assert_eq!(subset(3, &Value::empty_set()), "");
    }

    #[test]
    fn knows_tlcs_primes() {
        let primes = primes();
        assert_eq!((primes.len(), primes[0], primes[1340]), (1341, 1277011, 1295953));
    }
}
