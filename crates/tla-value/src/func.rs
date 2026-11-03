//! Functions: canonical construction, application, `DOMAIN`, and `EXCEPT`.

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::set::{search, sort_unique};
use crate::{Func, LazyFunc, Result, Symbol, Value, bail, fail};

/// The order a spec wrote the keys of a function in, as the index in [`Func::keys`] of each key.
pub(crate) struct WrittenOrder {
    indexes: Arc<[u32]>,
    /// Set once TLC would have normalized the function, after which it prints the keys sorted.
    is_normalized: AtomicBool,
}

impl WrittenOrder {
    /// The written order of `written` keys, unless they are already in the order of `sorted`.
    fn of(sorted: &[Value], written: &[Value]) -> Result<Option<Box<Self>>> {
        let mut indexes = Vec::with_capacity(written.len());
        for key in written {
            match search(sorted, key)? {
                Ok(index) => indexes.push(index as u32),
                Err(_) => return Ok(None),
            }
        }
        let is_sorted =
            indexes.iter().enumerate().all(|(position, &index)| index as usize == position);
        Ok((!is_sorted).then(|| {
            Box::new(Self { indexes: indexes.into(), is_normalized: AtomicBool::new(false) })
        }))
    }
}

impl Clone for WrittenOrder {
    fn clone(&self) -> Self {
        let is_normalized = self.is_normalized.load(Ordering::Relaxed);
        Self { indexes: self.indexes.clone(), is_normalized: AtomicBool::new(is_normalized) }
    }
}

impl Func {
    /// The keys and values in the order TLC prints them: as the spec wrote them until TLC
    /// normalizes the function, and sorted from then on.
    pub fn written_entries(&self) -> impl Iterator<Item = (&Value, &Value)> + '_ {
        let order = self
            .written
            .as_deref()
            .filter(|order| !order.is_normalized.load(Ordering::Relaxed))
            .map(|order| &order.indexes);
        (0..self.keys.len()).map(move |position| {
            let index = order.map_or(position, |indexes| indexes[position] as usize);
            (&self.keys[index], &self.values[index])
        })
    }

    /// Forgets the written order, as TLC sorts a function it compares or fingerprints.
    pub(crate) fn normalize(&self) {
        if let Some(order) = &self.written {
            order.is_normalized.store(true, Ordering::Relaxed);
        }
    }
}

/// One step of an `EXCEPT` path: `[arg]` or `.field`.
#[derive(Clone, Debug)]
pub enum Key {
    Apply(Value),
    Field(Symbol),
}

/// The keys of records with the fields `names`, sorted and distinct: one allocation for each
/// shape of record a thread builds, so that records of one shape share their keys.
fn record_keys(names: &[Symbol]) -> Arc<[Value]> {
    thread_local! {
        static SHAPES: RefCell<HashMap<Box<[Symbol]>, Arc<[Value]>>> = RefCell::default();
    }
    SHAPES.with_borrow_mut(|shapes| {
        if let Some(keys) = shapes.get(names) {
            return keys.clone();
        }
        let keys: Arc<[Value]> = names.iter().map(|name| Value::Str(*name)).collect();
        shapes.insert(names.into(), keys.clone());
        keys
    })
}

impl Value {
    /// The function mapping each key to its value. A function whose domain is `1..n` becomes a
    /// tuple. A repeated key keeps its first value.
    pub fn function(pairs: Vec<(Value, Value)>) -> Result<Value> {
        let is_tuple = pairs.iter().enumerate().all(
            |(index, (key, _))| matches!(key, Value::Int(key) if *key as i64 == index as i64 + 1),
        );
        if is_tuple {
            return Ok(Value::Tuple(pairs.into_iter().map(|(_, value)| value).collect()));
        }
        // Keys enumerated from a domain come sorted.
        let is_sorted = pairs
            .windows(2)
            .all(|pair| matches!(pair[0].0.compare(&pair[1].0), Ok(std::cmp::Ordering::Less)));
        if is_sorted {
            let (keys, values) = pairs.into_iter().unzip();
            return Ok(Self::from_sorted(keys, values));
        }
        let keys = sort_unique(pairs.iter().map(|(key, _)| key.clone()).collect())?;
        let mut values: Vec<Option<Value>> = vec![None; keys.len()];
        for (key, value) in pairs {
            let Ok(index) = search(&keys, &key)? else {
                unreachable!("every key of a pair is among the sorted keys")
            };
            values[index].get_or_insert(value);
        }
        let values = values.into_iter().map(|value| value.expect("every key has a pair"));
        Ok(Self::from_sorted(keys, values.collect()))
    }

    /// A function from keys already sorted and distinct.
    pub(crate) fn from_sorted(keys: Vec<Value>, values: Vec<Value>) -> Value {
        let is_tuple = keys
            .iter()
            .enumerate()
            .all(|(index, key)| matches!(key, Value::Int(key) if *key as i64 == index as i64 + 1));
        if is_tuple {
            return Value::Tuple(values.into());
        }
        Value::Func(Arc::new(Func { keys: keys.into(), values: values.into(), written: None }))
    }

    /// The record `[name |-> value, ...]`, which keeps the order its fields are written in.
    pub fn record(fields: Vec<(Symbol, Value)>) -> Value {
        if fields.is_empty() {
            return Value::empty_tuple();
        }
        if fields.windows(2).all(|pair| pair[0].0 < pair[1].0) {
            let (names, values): (Vec<Symbol>, Vec<Value>) = fields.into_iter().unzip();
            let keys = record_keys(&names);
            return Value::Func(Arc::new(Func { keys, values: values.into(), written: None }));
        }
        let written: Vec<Value> = fields.iter().map(|(name, _)| Value::Str(*name)).collect();
        let mut fields = fields;
        fields.sort_by_key(|(name, _)| *name);
        fields.dedup_by_key(|(name, _)| *name);
        let (names, values): (Vec<Symbol>, Vec<Value>) = fields.into_iter().unzip();
        let keys = record_keys(&names);
        // A record with a repeated field is sorted, as TLC builds it.
        let written = if keys.len() == written.len() {
            WrittenOrder::of(&keys, &written).expect("field names compare")
        } else {
            None
        };
        Value::Func(Arc::new(Func { keys, values: values.into(), written }))
    }

    /// The function `@@` builds from `pairs`, which keeps the order of keys that are all
    /// distinct strings, as TLC keeps it.
    pub fn written_function(pairs: Vec<(Value, Value)>) -> Result<Value> {
        let written: Vec<Value> = pairs.iter().map(|(key, _)| key.clone()).collect();
        let function = Value::function(pairs)?;
        let Value::Func(func) = &function else { return Ok(function) };
        let is_kept = func.keys.len() == written.len()
            && written.iter().all(|key| matches!(key, Value::Str(_)));
        let order = if is_kept { WrittenOrder::of(&func.keys, &written)? } else { None };
        let Some(order) = order else { return Ok(function) };
        let (keys, values) = (func.keys.clone(), func.values.clone());
        Ok(Value::Func(Arc::new(Func { keys, values, written: Some(order) })))
    }

    /// The pairs of a finite function in the order TLC prints them, as `@@` combines them.
    pub fn written_pairs(&self) -> Result<Vec<(Value, Value)>> {
        Ok(match self.materialize()? {
            Value::Tuple(items) => items
                .iter()
                .enumerate()
                .map(|(index, item)| (Value::Int(index as i32 + 1), item.clone()))
                .collect(),
            Value::Func(func) => {
                func.written_entries().map(|(key, value)| (key.clone(), value.clone())).collect()
            }
            other => {
                fail!([other], "Attempted to enumerate {other}, which is not a finite function")
            }
        })
    }

    /// The keys and values of a finite function, in key order.
    pub(crate) fn entries(&self) -> (Cow<'_, [Value]>, Cow<'_, [Value]>) {
        match self {
            Value::Tuple(items) => {
                let keys = (1..=items.len() as i32).map(Value::Int).collect::<Vec<_>>();
                (Cow::Owned(keys), Cow::Borrowed(items))
            }
            Value::Func(func) => (Cow::Borrowed(&func.keys), Cow::Borrowed(&func.values)),
            _ => (Cow::Owned(Vec::new()), Cow::Owned(Vec::new())),
        }
    }

    /// The finite function a lazy function stands for. Other values are returned as they are.
    pub fn materialize(&self) -> Result<Value> {
        let Value::LazyFunc(lazy) = self else { return Ok(self.clone()) };
        if !lazy.domain.is_enumerable() {
            // TLC sizes the domain first, which fails as the domain fails.
            lazy.domain.cardinality()?;
            bail!("Attempted to enumerate a function whose domain {} is infinite", lazy.domain);
        }
        let keys = lazy.domain.elements()?;
        let values = keys.iter().map(|key| (lazy.apply)(key)).collect::<Result<Vec<_>>>()?;
        Ok(Self::from_sorted(keys.to_vec(), values))
    }

    /// `self[arg]`.
    pub fn apply(&self, arg: &Value) -> Result<Value> {
        match self {
            Value::Tuple(items) => {
                if let Value::Int(index) = arg
                    && *index >= 1
                    && (*index as usize) <= items.len()
                {
                    return Ok(items[*index as usize - 1].clone());
                }
                fail!(
                    [self, arg],
                    "Attempted to apply tuple\n{self}\nto argument {arg}, which is out of bounds."
                )
            }
            Value::Func(func) => match search(&func.keys, arg)? {
                Ok(index) => Ok(func.values[index].clone()),
                Err(_) => fail!(
                    [self, arg],
                    "Attempted to apply function:\n{self}\nto argument {arg}, which is not in the domain of the function."
                ),
            },
            Value::LazyFunc(lazy) => {
                if !lazy.domain.contains(arg)? {
                    fail!(
                        [arg],
                        "Attempted to apply a function to {arg}, which is not in its domain"
                    );
                }
                (lazy.apply)(arg)
            }
            _ => fail!([self], "Attempted to apply {self}, which is not a function"),
        }
    }

    /// `self.name`.
    pub fn field(&self, name: Symbol) -> Result<Value> {
        match self {
            Value::Func(_) | Value::LazyFunc(_) => self.apply(&Value::Str(name)).map_err(|_| {
                crate::Error(format!(
                    "Attempted to access nonexistent field '{name}' of record\n{self}"
                ))
            }),
            _ => fail!(
                [self],
                "Attempted to access field '{name}' of {} {self}, which is not a record",
                self.kind()
            ),
        }
    }

    /// `DOMAIN self`.
    pub fn domain(&self) -> Result<Value> {
        match self {
            Value::Tuple(items) => Ok(Value::Interval(1, items.len() as i32)),
            Value::Func(func) => Ok(Value::Set(func.keys.clone())),
            Value::LazyFunc(lazy) => Ok(lazy.domain.clone()),
            _ => fail!([self], "DOMAIN expects a function but received {self}"),
        }
    }

    /// `[self EXCEPT !path = update(@)]`. A key outside the domain leaves the function as it is,
    /// as in TLC.
    pub fn except(
        &self,
        path: &[Key],
        update: &mut dyn FnMut(&Value) -> Result<Value>,
    ) -> Result<Value> {
        self.except_with(path, update, false)
    }

    /// `[self EXCEPT !path = update(@)]` where the result is applied at once, as in
    /// `[f EXCEPT ![1] = 2][1]`: TLC keeps a lazy function lazy then, whatever its domain.
    pub fn except_kept_lazy(
        &self,
        path: &[Key],
        update: &mut dyn FnMut(&Value) -> Result<Value>,
    ) -> Result<Value> {
        self.except_with(path, update, true)
    }

    fn except_with(
        &self,
        path: &[Key],
        update: &mut dyn FnMut(&Value) -> Result<Value>,
        is_kept_lazy: bool,
    ) -> Result<Value> {
        let Some((first, rest)) = path.split_first() else { return update(self) };
        let key = match first {
            Key::Apply(arg) => arg.clone(),
            Key::Field(name) => Value::Str(*name),
        };
        match self {
            Value::Tuple(items) => {
                let Value::Int(index) = key else {
                    if matches!(key, Value::Model(_)) {
                        return Ok(self.clone());
                    }
                    fail!(
                        [self, key],
                        "Attempted to apply EXCEPT to the tuple\n{self}\nwith the non-integer key {key}"
                    )
                };
                if index < 1 || index as usize > items.len() {
                    return Ok(self.clone());
                }
                let mut items = items.to_vec();
                items[index as usize - 1] = items[index as usize - 1].except(rest, update)?;
                Ok(Value::Tuple(items.into()))
            }
            Value::Func(func) => match search(&func.keys, &key)? {
                Ok(index) => {
                    let mut values = func.values.to_vec();
                    values[index] = values[index].except(rest, update)?;
                    Ok(Value::Func(Arc::new(Func {
                        keys: func.keys.clone(),
                        values: values.into(),
                        written: func.written.clone(),
                    })))
                }
                Err(_) => Ok(self.clone()),
            },
            Value::LazyFunc(lazy) => {
                if !is_kept_lazy && lazy.domain.is_enumerable() {
                    return self.materialize()?.except(path, update);
                }
                if !lazy.domain.contains(&key)? {
                    return Ok(self.clone());
                }
                let updated = (lazy.apply)(&key)?.except(rest, update)?;
                let previous = lazy.apply.clone();
                Ok(Value::LazyFunc(Arc::new(LazyFunc {
                    domain: lazy.domain.clone(),
                    apply: Arc::new(move |arg| {
                        if key.equals(arg)? { Ok(updated.clone()) } else { previous(arg) }
                    }),
                    source: None,
                })))
            }
            _ => fail!([self], "Attempted to apply EXCEPT construct to the value {self}."),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Key, Symbol, Value};

    #[test]
    fn builds_records_and_applies_them() {
        let record = Value::record(vec![
            (Symbol::intern("b"), Value::Int(2)),
            (Symbol::intern("a"), Value::Int(1)),
        ]);
        assert_eq!(record.field(Symbol::intern("b")).unwrap().as_int(), Some(2));
        assert!(record.field(Symbol::intern("c")).is_err());
        assert_eq!(record.domain().unwrap().cardinality().unwrap(), 2);
    }

    #[test]
    fn updates_nested_paths() {
        let inner = Value::tuple(vec![Value::Int(1), Value::Int(2)]);
        let outer = Value::record(vec![(Symbol::intern("x"), inner)]);
        let path = [Key::Field(Symbol::intern("x")), Key::Apply(Value::Int(2))];
        let updated =
            outer.except(&path, &mut |old| Ok(Value::Int(old.as_int().unwrap() + 10))).unwrap();
        assert_eq!(updated.to_string(), "[x |-> <<1, 12>>]");
        let missing = [Key::Field(Symbol::intern("y"))];
        assert_eq!(
            outer.except(&missing, &mut |_| Ok(Value::TRUE)).unwrap().to_string(),
            "[x |-> <<1, 2>>]"
        );
    }

    /// Materializing a function over a domain TLC can't enumerate fails as sizing the domain
    /// does, and printing such a function doesn't recurse into that failure.
    #[test]
    fn refuses_to_materialize_an_infinite_domain() {
        let function = Value::LazyFunc(std::sync::Arc::new(crate::LazyFunc {
            domain: Value::lazy(crate::LazySet::Nat),
            apply: std::sync::Arc::new(|_| Ok(Value::Int(0))),
            source: None,
        }));
        assert_eq!(
            function.materialize().unwrap_err().0,
            "Attempted to compute the number of elements in the overridden value Nat."
        );
        assert!(!function.to_string().is_empty());
    }

    /// Two field names interned so that the second sorts before the first, as TLC orders strings
    /// by when it first interned them.
    fn reversed_names(prefix: &str) -> (Symbol, Symbol) {
        let later = Symbol::intern(&format!("{prefix}_later"));
        let earlier = Symbol::intern(&format!("{prefix}_earlier"));
        (earlier, later)
    }

    /// tla-ts's NormalizationCases: TLC prints a record in the order its fields are written
    /// until it compares or fingerprints it, and the order never decides equality.
    #[test]
    fn keeps_the_written_order_of_records_until_normalized() {
        let (first, second) = reversed_names("written_record");
        let record = Value::record(vec![(first, Value::Int(1)), (second, Value::Int(2))]);
        assert_eq!(
            record.to_string(),
            "[written_record_earlier |-> 1, written_record_later |-> 2]"
        );
        let reversed = Value::record(vec![(second, Value::Int(2)), (first, Value::Int(1))]);
        assert_eq!(
            reversed.to_string(),
            "[written_record_later |-> 2, written_record_earlier |-> 1]"
        );
        let updated = record.except(&[Key::Field(second)], &mut |_| Ok(Value::Int(3))).unwrap();
        assert_eq!(
            updated.to_string(),
            "[written_record_earlier |-> 1, written_record_later |-> 3]"
        );
        assert!(record.equals(&reversed).unwrap());
        assert_eq!(
            record.to_string(),
            "[written_record_later |-> 2, written_record_earlier |-> 1]"
        );
        let fingerprinted = Value::record(vec![(first, Value::Int(1)), (second, Value::Int(2))]);
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        fingerprinted.fingerprint(&mut hasher).unwrap();
        assert_eq!(fingerprinted.to_string(), reversed.to_string());
    }

    #[test]
    fn keeps_the_order_of_string_keys_that_combine() {
        let (first, second) = reversed_names("written_function");
        let pairs = vec![(Value::Str(first), Value::Int(0)), (Value::Str(second), Value::Int(0))];
        let combined = Value::written_function(pairs).unwrap();
        assert_eq!(
            combined.to_string(),
            "[written_function_earlier |-> 0, written_function_later |-> 0]"
        );
        assert_eq!(
            combined
                .written_pairs()
                .unwrap()
                .iter()
                .map(|(key, _)| key.to_string())
                .collect::<Vec<_>>(),
            ["\"written_function_earlier\"", "\"written_function_later\""]
        );
        let repeated = Value::written_function(vec![
            (Value::Str(first), Value::Int(0)),
            (Value::Str(second), Value::Int(1)),
            (Value::Str(first), Value::Int(2)),
        ])
        .unwrap();
        assert_eq!(
            repeated.to_string(),
            "[written_function_later |-> 1, written_function_earlier |-> 0]"
        );
    }
}
