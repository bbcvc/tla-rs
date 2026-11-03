//! Functions: canonical construction, application, `DOMAIN`, and `EXCEPT`.

use std::borrow::Cow;
use std::sync::Arc;

use crate::set::{search, sort_unique};
use crate::{Func, LazyFunc, Result, Symbol, Value, bail};

/// One step of an `EXCEPT` path: `[arg]` or `.field`.
#[derive(Clone, Debug)]
pub enum Key {
    Apply(Value),
    Field(Symbol),
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
        let keys = sort_unique(pairs.iter().map(|(key, _)| key.clone()).collect())?;
        let mut values = Vec::with_capacity(keys.len());
        for key in &keys {
            let mut found = None;
            for (candidate, value) in &pairs {
                if candidate.equals(key)? {
                    found = Some(value.clone());
                    break;
                }
            }
            values.push(found.expect("every sorted key comes from a pair"));
        }
        Ok(Self::from_sorted(keys, values))
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
        Value::Func(Arc::new(Func { keys: keys.into(), values: values.into() }))
    }

    /// The record `[name |-> value, ...]`.
    pub fn record(fields: Vec<(Symbol, Value)>) -> Value {
        let mut fields = fields;
        fields.sort_by_key(|(name, _)| *name);
        fields.dedup_by_key(|(name, _)| *name);
        let (keys, values) =
            fields.into_iter().map(|(name, value)| (Value::Str(name), value)).unzip();
        Self::from_sorted(keys, values)
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
                bail!(
                    "Attempted to apply tuple\n{self}\nto argument {arg}, which is out of bounds."
                )
            }
            Value::Func(func) => match search(&func.keys, arg)? {
                Ok(index) => Ok(func.values[index].clone()),
                Err(_) => bail!(
                    "Attempted to apply function:\n{self}\nto argument {arg}, which is not in the domain of the function."
                ),
            },
            Value::LazyFunc(lazy) => {
                if !lazy.domain.contains(arg)? {
                    bail!("Attempted to apply a function to {arg}, which is not in its domain");
                }
                (lazy.apply)(arg)
            }
            _ => bail!("Attempted to apply {self}, which is not a function"),
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
            _ => bail!(
                "Attempted to access field '{name}' of {} {self}, which is not a record",
                self.kind()
            ),
        }
    }

    /// `DOMAIN self`.
    pub fn domain(&self) -> Result<Value> {
        match self {
            Value::Tuple(items) => Ok(Value::Interval(1, items.len() as i32)),
            Value::Func(func) => Ok(Value::Set(func.keys.to_vec().into())),
            Value::LazyFunc(lazy) => Ok(lazy.domain.clone()),
            _ => bail!("DOMAIN expects a function but received {self}"),
        }
    }

    /// `[self EXCEPT !path = update(@)]`. A key outside the domain leaves the function as it is,
    /// as in TLC.
    pub fn except(
        &self,
        path: &[Key],
        update: &mut dyn FnMut(&Value) -> Result<Value>,
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
                    bail!(
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
                    })))
                }
                Err(_) => Ok(self.clone()),
            },
            Value::LazyFunc(lazy) => {
                if lazy.domain.is_enumerable() {
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
                        if arg.equals(&key)? { Ok(updated.clone()) } else { previous(arg) }
                    }),
                })))
            }
            _ => bail!("Attempted to apply EXCEPT construct to the value {self}."),
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
        }));
        assert_eq!(
            function.materialize().unwrap_err().0,
            "Attempted to compute the number of elements in the overridden value Nat."
        );
        assert!(!function.to_string().is_empty());
    }
}
