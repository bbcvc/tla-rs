//! Fingerprints that agree with [`Value::equals`]: equal values hash alike whatever their
//! representation, so `1..3` and `{1, 2, 3}` share a fingerprint, as TLC's do.

use std::hash::{Hash, Hasher};

use crate::{Result, Symbol, Value};

impl Value {
    /// Feeds the canonical form of the value to `state`. Fails for a value TLC can't
    /// fingerprint, such as an infinite set or a set it can't sort.
    pub fn fingerprint<H: Hasher>(&self, state: &mut H) -> Result<()> {
        match self {
            Value::Bool(value) => {
                0u8.hash(state);
                value.hash(state);
            }
            Value::Int(value) => {
                1u8.hash(state);
                value.hash(state);
            }
            Value::Str(text) => {
                2u8.hash(state);
                text.hash(state);
            }
            Value::Model(name) => {
                3u8.hash(state);
                name.hash(state);
            }
            Value::Set(elements) => hash_set(elements, state)?,
            Value::MixedSet(_) | Value::Interval(..) => hash_set(&self.elements()?, state)?,
            Value::Lazy(_) => {
                let elements = self.elements()?;
                // TLC's `fingerPrint` of a lazy set caches its elements.
                self.cache_elements();
                hash_set(&elements, state)?
            }
            Value::Tuple(items) => {
                4u8.hash(state);
                items.len().hash(state);
                for (index, item) in items.iter().enumerate() {
                    Value::Int(index as i32 + 1).fingerprint(state)?;
                    item.fingerprint(state)?;
                }
            }
            Value::Func(func) => {
                func.normalize();
                4u8.hash(state);
                func.keys.len().hash(state);
                for (key, value) in func.keys.iter().zip(func.values.iter()) {
                    key.fingerprint(state)?;
                    value.fingerprint(state)?;
                }
            }
            Value::LazyFunc(_) => self.materialize()?.fingerprint(state)?,
        }
        Ok(())
    }
}

impl Value {
    /// Feeds the canonical form of `self.permute(image)` to `state`, as
    /// [`Value::fingerprint`] would, without building the permuted value where it can: a tuple,
    /// or a function whose domain the permutation keeps, is fed part by part.
    pub fn fingerprint_permuted<H: Hasher>(
        &self,
        image: &impl Fn(Symbol) -> Option<Value>,
        state: &mut H,
    ) -> Result<()> {
        match self {
            Value::Model(name) => match image(*name) {
                Some(permuted) => permuted.fingerprint(state)?,
                None => self.fingerprint(state)?,
            },
            Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => {
                self.fingerprint(state)?
            }
            Value::Tuple(items) => {
                4u8.hash(state);
                items.len().hash(state);
                for (index, item) in items.iter().enumerate() {
                    Value::Int(index as i32 + 1).fingerprint(state)?;
                    item.fingerprint_permuted(image, state)?;
                }
            }
            Value::Func(func) => match kept_domain_sources(&func.keys, image) {
                Some(sources) => {
                    4u8.hash(state);
                    func.keys.len().hash(state);
                    for (key, source) in func.keys.iter().zip(sources) {
                        key.fingerprint(state)?;
                        func.values[source].fingerprint_permuted(image, state)?;
                    }
                }
                None => self.permute(image)?.fingerprint(state)?,
            },
            Value::Set(_) | Value::MixedSet(_) | Value::Lazy(_) | Value::LazyFunc(_) => {
                self.permute(image)?.fingerprint(state)?
            }
        }
        Ok(())
    }
}

/// Where the permuted function takes the value of each of its keys `keys` from, when the
/// permutation maps them onto themselves: the index of the key each is the image of.
fn kept_domain_sources(
    keys: &[Value],
    image: &impl Fn(Symbol) -> Option<Value>,
) -> Option<Vec<usize>> {
    if !keys.iter().any(|key| key.moves(image)) {
        return Some((0..keys.len()).collect());
    }
    let model_image = |key: &Value| match key {
        Value::Model(name) => Some(image(*name).unwrap_or_else(|| key.clone())),
        _ => None,
    };
    let images: Vec<Value> = keys.iter().map(model_image).collect::<Option<_>>()?;
    keys.iter()
        .map(|key| {
            images.iter().position(|image| match (image, key) {
                (Value::Model(image), Value::Model(key)) => image == key,
                _ => false,
            })
        })
        .collect()
}

fn hash_set<H: Hasher>(elements: &[Value], state: &mut H) -> Result<()> {
    5u8.hash(state);
    elements.len().hash(state);
    for element in elements {
        element.fingerprint(state)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hasher;

    use crate::Value;

    fn fingerprint(value: &Value) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.fingerprint(&mut hasher).unwrap();
        hasher.finish()
    }

    #[test]
    fn agrees_with_equality() {
        let explicit = Value::set(vec![Value::Int(1), Value::Int(2), Value::Int(3)]).unwrap();
        assert_eq!(fingerprint(&Value::Interval(1, 3)), fingerprint(&explicit));
        let function = Value::function(vec![(Value::Int(1), Value::TRUE)]).unwrap();
        assert_eq!(fingerprint(&function), fingerprint(&Value::tuple(vec![Value::TRUE])));
        assert_ne!(fingerprint(&Value::empty_set()), fingerprint(&Value::empty_tuple()));
    }
}
