//! Values with model values replaced, as TLC permutes a state under a symmetry.

use std::cmp::Ordering;
use std::sync::Arc;

use crate::{Func, Result, Symbol, Value};

impl Value {
    /// The value with each model value `image` maps replaced by its image, as TLC's `permute`
    /// gives it: sets and function domains sorted again. A part without such a model value is
    /// kept as it is.
    pub fn permute(&self, image: &impl Fn(Symbol) -> Option<Value>) -> Result<Value> {
        Ok(self.permuted(image)?.unwrap_or_else(|| self.clone()))
    }

    /// The permuted value, or `None` where the permutation leaves the value as it is.
    fn permuted(&self, image: &impl Fn(Symbol) -> Option<Value>) -> Result<Option<Value>> {
        Ok(match self {
            Value::Model(name) => image(*name),
            Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => None,
            Value::Tuple(items) => {
                permuted_all(items, image)?.map(|items| Value::Tuple(items.into()))
            }
            Value::Func(func) => {
                let keys = permuted_all(&func.keys, image)?;
                let values = permuted_all(&func.values, image)?;
                match (keys, values) {
                    (None, None) => None,
                    // The domain stays sorted.
                    (None, Some(values)) => Some(Value::Func(Arc::new(Func {
                        keys: func.keys.clone(),
                        values: values.into(),
                        written: func.written.clone(),
                    }))),
                    (Some(images), values) => {
                        let values = values.unwrap_or_else(|| func.values.to_vec());
                        // A permutation that maps the domain onto itself keeps it: the value at
                        // each key is that of the key it is the image of.
                        let sources: Option<Vec<usize>> = func
                            .keys
                            .iter()
                            .map(|key| images.iter().position(|image| is_same_model(image, key)))
                            .collect();
                        match sources {
                            Some(sources) => Some(Value::Func(Arc::new(Func {
                                keys: func.keys.clone(),
                                values: sources
                                    .into_iter()
                                    .map(|source| values[source].clone())
                                    .collect(),
                                written: func.written.clone(),
                            }))),
                            None => {
                                Some(Value::function(images.into_iter().zip(values).collect())?)
                            }
                        }
                    }
                }
            }
            Value::LazyFunc(_) => {
                let function = self.materialize()?;
                Some(function.permuted(image)?.unwrap_or(function))
            }
            Value::Set(elements) => match permuted_all(elements, image)? {
                Some(elements) => Some(Value::set(elements)?),
                None => None,
            },
            Value::MixedSet(_) | Value::Lazy(_) => match permuted_all(&self.elements()?, image)? {
                Some(elements) => Some(Value::set(elements)?),
                None => None,
            },
        })
    }
}

impl Value {
    /// `self.permute(image).compare(other)`, without building the parts of the permuted value
    /// the comparison doesn't need. `preimage` gives the model value `image` maps to a model
    /// value, if any, as a permutation of model values has one.
    pub fn compare_permuted(
        &self,
        image: &impl Fn(Symbol) -> Option<Value>,
        preimage: &impl Fn(Symbol) -> Option<Symbol>,
        other: &Value,
    ) -> Result<Ordering> {
        match (self, other) {
            (Value::Model(name), _) => match image(*name) {
                Some(permuted) => permuted.compare(other),
                None => self.compare(other),
            },
            (Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..), _) => {
                self.compare(other)
            }
            // A permutation keeps the size of a tuple, a set, or a function, which they compare
            // by first.
            (Value::Tuple(items), Value::Tuple(others)) if items.len() != others.len() => {
                Ok(items.len().cmp(&others.len()))
            }
            (Value::Set(elements), Value::Set(others)) if elements.len() != others.len() => {
                Ok(elements.len().cmp(&others.len()))
            }
            (Value::Func(func), Value::Func(others))
                if func.keys.len() != others.keys.len()
                    && is_record(&func.keys) == is_record(&others.keys) =>
            {
                func.normalize();
                others.normalize();
                Ok(func.keys.len().cmp(&others.keys.len()))
            }
            (Value::Tuple(items), Value::Tuple(others)) => {
                for (item, other) in items.iter().zip(others.iter()) {
                    let ordering = item.compare_permuted(image, preimage, other)?;
                    if ordering != Ordering::Equal {
                        return Ok(ordering);
                    }
                }
                Ok(Ordering::Equal)
            }
            (Value::Func(func), Value::Func(others)) => {
                match permuted_sources(func, others, image, preimage)? {
                    Some(sources) => {
                        // As comparing the functions does.
                        func.normalize();
                        others.normalize();
                        for (source, other) in sources.into_iter().zip(others.values.iter()) {
                            let value = &func.values[source];
                            let ordering = value.compare_permuted(image, preimage, other)?;
                            if ordering != Ordering::Equal {
                                return Ok(ordering);
                            }
                        }
                        Ok(Ordering::Equal)
                    }
                    None => self.permute(image)?.compare(other),
                }
            }
            (Value::Set(elements), _) if !elements.iter().any(|element| element.moves(image)) => {
                self.compare(other)
            }
            // Sets of one size, whose permuted elements compare in their order.
            (Value::Set(elements), Value::Set(others)) => match &elements[..] {
                [element] => element.compare_permuted(image, preimage, &others[0]),
                _ => {
                    let mut permuted = elements
                        .iter()
                        .map(|element| element.permute(image))
                        .collect::<Result<Vec<_>>>()?;
                    let mut failure = None;
                    permuted.sort_by(|left, right| {
                        left.compare(right).unwrap_or_else(|error| {
                            failure.get_or_insert(error);
                            Ordering::Equal
                        })
                    });
                    if let Some(error) = failure {
                        return Err(error);
                    }
                    for (element, other) in permuted.iter().zip(others.iter()) {
                        let ordering = element.compare(other)?;
                        if ordering != Ordering::Equal {
                            return Ok(ordering);
                        }
                    }
                    Ok(Ordering::Equal)
                }
            },
            _ => self.permute(image)?.compare(other),
        }
    }

    /// Whether the permutation moves a model value the value holds.
    fn moves(&self, image: &impl Fn(Symbol) -> Option<Value>) -> bool {
        match self {
            Value::Model(name) => image(*name).is_some(),
            Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => false,
            Value::Tuple(items) | Value::Set(items) | Value::MixedSet(items) => {
                items.iter().any(|item| item.moves(image))
            }
            Value::Func(func) => {
                func.keys.iter().chain(func.values.iter()).any(|value| value.moves(image))
            }
            Value::Lazy(_) | Value::LazyFunc(_) => true,
        }
    }
}

/// Where the permuted function `func` takes the value of each key of `others` from: the index
/// in `func` of the key's preimage. `None` unless `func` and `others` have the same keys, which
/// the permutation maps onto themselves, so that the permuted function has them too.
fn permuted_sources(
    func: &Func,
    others: &Func,
    image: &impl Fn(Symbol) -> Option<Value>,
    preimage: &impl Fn(Symbol) -> Option<Symbol>,
) -> Result<Option<Vec<usize>>> {
    if func.keys.len() != others.keys.len() {
        return Ok(None);
    }
    if !std::ptr::eq(func, others) {
        for (key, other) in func.keys.iter().zip(others.keys.iter()) {
            if key.compare(other)? != Ordering::Equal {
                return Ok(None);
            }
        }
    }
    let mut sources = Vec::with_capacity(func.keys.len());
    for (index, key) in func.keys.iter().enumerate() {
        let source = match key {
            Value::Model(name) => match preimage(*name) {
                Some(from) => {
                    let found = func
                        .keys
                        .iter()
                        .position(|key| matches!(key, Value::Model(name) if *name == from));
                    match found {
                        Some(source) => source,
                        None => return Ok(None),
                    }
                }
                None => index,
            },
            _ if key.moves(image) => return Ok(None),
            _ => index,
        };
        sources.push(source);
    }
    Ok(Some(sources))
}

/// Whether the keys are those of a record, which TLC compares only with a record.
fn is_record(keys: &[Value]) -> bool {
    keys.iter().all(|key| matches!(key, Value::Str(_)))
}

/// Whether two values are the same model value.
fn is_same_model(left: &Value, right: &Value) -> bool {
    matches!((left, right), (Value::Model(left), Value::Model(right)) if left == right)
}

/// The permuted values, or `None` when the permutation leaves each as it is.
fn permuted_all(
    values: &[Value],
    image: &impl Fn(Symbol) -> Option<Value>,
) -> Result<Option<Vec<Value>>> {
    let mut changed: Option<Vec<Value>> = None;
    for (index, value) in values.iter().enumerate() {
        match (value.permuted(image)?, &mut changed) {
            (Some(permuted), Some(changed)) => changed.push(permuted),
            (Some(permuted), None) => {
                let mut changed_values = Vec::with_capacity(values.len());
                changed_values.extend_from_slice(&values[..index]);
                changed_values.push(permuted);
                changed = Some(changed_values);
            }
            (None, Some(changed)) => changed.push(value.clone()),
            (None, None) => {}
        }
    }
    Ok(changed)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn model(name: &str) -> Value {
        Value::Model(Symbol::intern(name))
    }

    /// Swaps `a` and `b`.
    fn swap(name: Symbol) -> Option<Value> {
        match name.as_str() {
            "a" => Some(model("b")),
            "b" => Some(model("a")),
            _ => None,
        }
    }

    #[test]
    fn replaces_model_values_and_sorts_again() {
        let (a, b, c) = (model("a"), model("b"), model("c"));
        let set = Value::set(vec![a.clone(), c.clone()]).unwrap();
        assert!(
            set.permute(&swap)
                .unwrap()
                .equals(&Value::set(vec![b.clone(), c.clone()]).unwrap())
                .unwrap()
        );
        let function =
            Value::function(vec![(a.clone(), Value::Int(1)), (c.clone(), b.clone())]).unwrap();
        let expected =
            Value::function(vec![(b.clone(), Value::Int(1)), (c.clone(), a.clone())]).unwrap();
        assert!(function.permute(&swap).unwrap().equals(&expected).unwrap());
        // A domain the permutation maps onto itself.
        let closed = Value::function(vec![
            (a.clone(), Value::Int(1)),
            (b.clone(), Value::Int(2)),
            (c.clone(), a.clone()),
        ])
        .unwrap();
        let expected = Value::function(vec![
            (b.clone(), Value::Int(1)),
            (a.clone(), Value::Int(2)),
            (c.clone(), b.clone()),
        ])
        .unwrap();
        assert!(closed.permute(&swap).unwrap().equals(&expected).unwrap());
        let tuple = Value::tuple(vec![Value::Int(1), a.clone()]);
        assert_eq!(
            tuple.permute(&swap).unwrap().to_string(),
            Value::tuple(vec![Value::Int(1), b]).to_string()
        );
    }

    fn preimage_of_swap(name: Symbol) -> Option<Symbol> {
        swap(name).map(|value| match value {
            Value::Model(name) => name,
            _ => unreachable!("a swap maps model values to model values"),
        })
    }

    /// Comparing a permuted value with another agrees with permuting it and comparing.
    #[test]
    fn compares_permuted_values_as_permuting_and_comparing() {
        let (a, b, c) = (model("a"), model("b"), model("c"));
        let function = |pairs: &[(&Value, Value)]| {
            Value::function(
                pairs.iter().map(|(key, value)| ((*key).clone(), value.clone())).collect(),
            )
            .unwrap()
        };
        let set = |values: &[&Value]| {
            Value::set(values.iter().map(|&value| value.clone()).collect()).unwrap()
        };
        let record = |a_value: Value, b_value: Value| {
            Value::record(vec![(Symbol::intern("x"), a_value), (Symbol::intern("y"), b_value)])
        };
        let values = vec![
            a.clone(),
            c.clone(),
            Value::Int(3),
            Value::tuple(vec![a.clone(), Value::Int(1)]),
            Value::tuple(vec![b.clone(), Value::Int(1)]),
            function(&[(&a, Value::Int(1)), (&b, Value::Int(2)), (&c, Value::Int(3))]),
            function(&[(&a, Value::Int(2)), (&b, Value::Int(1)), (&c, Value::Int(3))]),
            function(&[(&a, b.clone()), (&b, a.clone()), (&c, c.clone())]),
            function(&[(&a, Value::Int(1)), (&c, Value::Int(3))]),
            function(&[(&b, Value::Int(1)), (&c, Value::Int(3))]),
            set(&[&a, &c]),
            set(&[&b, &c]),
            set(&[&c]),
            record(a.clone(), set(&[&b])),
            record(b.clone(), set(&[&a])),
            function(&[(&Value::tuple(vec![a.clone()]), Value::Int(1))]),
        ];
        for value in &values {
            for other in &values {
                let expected = value.permute(&swap).unwrap().compare(other);
                let compared = value.compare_permuted(&swap, &preimage_of_swap, other);
                match (expected, compared) {
                    (Ok(expected), Ok(compared)) => {
                        assert_eq!(expected, compared, "{value} permuted against {other}")
                    }
                    (Err(expected), Err(compared)) => assert_eq!(expected.0, compared.0),
                    (expected, compared) => {
                        panic!("{value} against {other}: {expected:?} but {compared:?}")
                    }
                }
            }
        }
    }

    #[test]
    fn keeps_what_the_permutation_leaves() {
        let set = Value::set(vec![model("c"), model("d")]).unwrap();
        let Value::Set(before) = &set else { panic!("a set") };
        let Value::Set(after) = set.permute(&swap).unwrap() else { panic!("a set") };
        assert!(Arc::ptr_eq(before, &after));
    }
}
