//! What tells two states apart for the model checker: the values of the variables, or the value
//! of the `VIEW`, under the permutations of the `SYMMETRY`, as TLC fingerprints them.
//!
//! TLC fingerprints a state of a symmetric spec by a representative of its orbit, the states its
//! permutations give, so a state and its permutations count once. Any choice of representative
//! that is the same for the whole orbit counts the same states, so this takes the smallest
//! fingerprint of the orbit. TLC closes the permutations the `SYMMETRY` gives under
//! composition, as does this.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::{BuildHasher, Hasher};
use std::sync::Arc;

use tla_eval::{Evaluator, State};
use tla_resolve::{DefId, RootName};
use tla_value::{Symbol, Value};

use crate::Error;

/// A permutation of model values.
type Permutation = HashMap<Symbol, Value>;

pub struct Fingerprinter {
    view: Option<DefId>,
    /// The permutations other than the identity.
    permutations: Vec<Permutation>,
}

impl Fingerprinter {
    /// The fingerprinter of a model with the `VIEW` and `SYMMETRY` its configuration names.
    pub fn new(
        evaluator: &Evaluator,
        view: Option<DefId>,
        symmetry: Option<Symbol>,
    ) -> Result<Self, Error> {
        let permutations = match symmetry {
            Some(name) => symmetry_group(evaluator, name)?,
            None => Vec::new(),
        };
        Ok(Self { view, permutations })
    }

    /// The fingerprint of `state`.
    pub fn fingerprint(&self, evaluator: &Evaluator, state: &State) -> Result<u128, String> {
        let mut smallest = self.fingerprint_one(evaluator, state)?;
        for permutation in &self.permutations {
            let permuted: Vec<Value> =
                state.iter().map(|value| permute(value, permutation)).collect::<Result<_, _>>()?;
            let fingerprint = self.fingerprint_one(evaluator, &Arc::from(permuted))?;
            smallest = smallest.min(fingerprint);
        }
        Ok(smallest)
    }

    /// TLC's own fingerprint of `state`, or of its view, which orders the successors of a
    /// state in the behavior graph of liveness checking.
    pub fn tlc(&self, evaluator: &Evaluator, state: &State) -> Result<u64, String> {
        match self.view {
            Some(view) => {
                let value =
                    evaluator.eval_def(view, Some(state)).map_err(|error| error.to_string())?;
                tla_eval::tlc_fingerprint(std::slice::from_ref(&value))
            }
            None => tla_eval::tlc_fingerprint(state),
        }
    }

    fn fingerprint_one(&self, evaluator: &Evaluator, state: &State) -> Result<u128, String> {
        match self.view {
            Some(view) => {
                let value =
                    evaluator.eval_def(view, Some(state)).map_err(|error| error.to_string())?;
                hash(std::slice::from_ref(&value))
            }
            None => hash(state),
        }
    }
}

/// A fingerprint that agrees with value equality, wide enough that two distinct states don't
/// share one in practice: two independently seeded 64-bit hashes of one pass over the values.
pub fn hash(values: &[Value]) -> Result<u128, String> {
    let mut hasher = Wide::new();
    for value in values {
        value.fingerprint(&mut hasher).map_err(|error| error.to_string())?;
    }
    Ok(hasher.finish_wide())
}

/// Two hashers with different seeds fed the same writes.
struct Wide {
    low: foldhash::quality::FoldHasher<'static>,
    high: foldhash::quality::FoldHasher<'static>,
}

impl Wide {
    fn new() -> Self {
        Self {
            low: foldhash::quality::FixedState::with_seed(0x243f_6a88_85a3_08d3).build_hasher(),
            high: foldhash::quality::FixedState::with_seed(0x1319_8a2e_0370_7344).build_hasher(),
        }
    }

    fn finish_wide(&self) -> u128 {
        (u128::from(self.high.finish()) << 64) | u128::from(self.low.finish())
    }
}

impl Hasher for Wide {
    fn finish(&self) -> u64 {
        self.low.finish()
    }

    fn write(&mut self, bytes: &[u8]) {
        self.low.write(bytes);
        self.high.write(bytes);
    }

    fn write_u8(&mut self, value: u8) {
        self.low.write_u8(value);
        self.high.write_u8(value);
    }

    fn write_u32(&mut self, value: u32) {
        self.low.write_u32(value);
        self.high.write_u32(value);
    }

    fn write_u64(&mut self, value: u64) {
        self.low.write_u64(value);
        self.high.write_u64(value);
    }

    fn write_usize(&mut self, value: usize) {
        self.low.write_usize(value);
        self.high.write_usize(value);
    }

    fn write_i64(&mut self, value: i64) {
        self.write_u64(value as u64);
    }
}

/// The permutations the symmetry definition gives, closed under composition, without the
/// identity. TLC's `Tool.getSymmetryPerms`.
fn symmetry_group(evaluator: &Evaluator, name: Symbol) -> Result<Vec<Permutation>, Error> {
    let spec = evaluator.spec();
    let not_defined = || {
        Error::config(format!(
            "The symmetry function {name} specified in the configuration file\nis not defined in the specification."
        ))
    };
    let def = match spec.lookup(name.as_str()) {
        Some(RootName::Def(def)) => def,
        Some(_) => {
            return Err(Error::config(format!(
                "The symmetry function {name} must specify a set of permutations."
            )));
        }
        None => return Err(not_defined()),
    };
    if !spec.def(def).params.is_empty() {
        return Err(Error::config(format!(
            "The symmetry function {name} must specify a set of permutations."
        )));
    }
    let value = evaluator.eval_def(def, None).map_err(|error| Error::config(error.to_string()))?;
    let elements = value
        .elements()
        .map_err(|_| Error::config("The symmetry operator must specify a set of functions."))?;
    let mut generators = Vec::new();
    for element in elements.iter() {
        let pairs = element
            .written_pairs()
            .map_err(|_| Error::config("The symmetry values must be function records."))?;
        let permutation: BTreeMap<Symbol, Value> = pairs
            .into_iter()
            .filter_map(|(from, to)| match from {
                Value::Model(from) if !is_model(&to, from) => Some((from, to)),
                _ => None,
            })
            .collect();
        if !permutation.is_empty() {
            generators.push(permutation);
        }
    }
    let mut group: Vec<BTreeMap<Symbol, Value>> = Vec::new();
    let mut seen: HashSet<Vec<(Symbol, String)>> = HashSet::new();
    let key = |permutation: &BTreeMap<Symbol, Value>| {
        permutation.iter().map(|(from, to)| (*from, to.to_string())).collect::<Vec<_>>()
    };
    for generator in &generators {
        if seen.insert(key(generator)) {
            group.push(generator.clone());
        }
    }
    let mut start = 0;
    while start < group.len() {
        let end = group.len();
        for generator in &generators {
            for member in start..end {
                let composed = compose(generator, &group[member]);
                if !composed.is_empty() && seen.insert(key(&composed)) {
                    group.push(composed);
                }
            }
        }
        start = end;
    }
    Ok(group.into_iter().map(|permutation| permutation.into_iter().collect()).collect())
}

/// `outer` after `inner`, without the model values it leaves in place.
fn compose(
    outer: &BTreeMap<Symbol, Value>,
    inner: &BTreeMap<Symbol, Value>,
) -> BTreeMap<Symbol, Value> {
    let image = |from: Symbol| {
        let middle = inner.get(&from).cloned().unwrap_or(Value::Model(from));
        match &middle {
            Value::Model(name) => outer.get(name).cloned().unwrap_or(middle),
            _ => middle,
        }
    };
    let moved: HashSet<Symbol> = outer.keys().chain(inner.keys()).copied().collect();
    moved
        .into_iter()
        .filter_map(|from| {
            let to = image(from);
            (!is_model(&to, from)).then_some((from, to))
        })
        .collect()
}

fn is_model(value: &Value, name: Symbol) -> bool {
    matches!(value, Value::Model(found) if *found == name)
}

/// `value` with each model value the permutation moves replaced by its image.
fn permute(value: &Value, permutation: &Permutation) -> Result<Value, String> {
    let error = |error: tla_value::Error| error.to_string();
    Ok(match value {
        Value::Model(name) => permutation.get(name).cloned().unwrap_or_else(|| value.clone()),
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => value.clone(),
        Value::Tuple(items) => Value::tuple(
            items.iter().map(|item| permute(item, permutation)).collect::<Result<_, _>>()?,
        ),
        Value::Func(_) | Value::LazyFunc(_) => {
            let pairs = value.written_pairs().map_err(error)?;
            let pairs = pairs
                .iter()
                .map(|(key, value)| Ok((permute(key, permutation)?, permute(value, permutation)?)))
                .collect::<Result<Vec<_>, String>>()?;
            Value::function(pairs).map_err(error)?
        }
        _ => {
            let elements = value.elements().map_err(error)?;
            let permuted = elements
                .iter()
                .map(|element| permute(element, permutation))
                .collect::<Result<Vec<_>, _>>()?;
            Value::set(permuted).map_err(error)?
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testing;

    fn evaluator(body: &str, config: &str) -> Evaluator {
        let spec = testing::spec(body);
        let config = tla_parser::parse_config(config).unwrap_or_else(|error| panic!("{error}"));
        let model =
            tla_eval::bind_model(&spec, &config).unwrap_or_else(|error| panic!("{error:?}"));
        Evaluator::new(Arc::new(spec), model.constants).with_overrides(model.overrides)
    }

    fn model(name: &str) -> Value {
        Value::Model(Symbol::intern(name))
    }

    fn fingerprint(fingerprinter: &Fingerprinter, evaluator: &Evaluator, value: Value) -> u128 {
        fingerprinter.fingerprint(evaluator, &Arc::from(vec![value])).unwrap()
    }

    #[test]
    fn tells_states_apart_by_the_view() {
        let evaluator = evaluator("View == x % 2", "");
        let Some(RootName::Def(view)) = evaluator.spec().lookup("View") else { panic!("View") };
        let fingerprinter = Fingerprinter::new(&evaluator, Some(view), None).unwrap();
        let of = |x| fingerprint(&fingerprinter, &evaluator, Value::Int(x));
        assert_eq!(of(0), of(2));
        assert_ne!(of(0), of(1));
        let plain = Fingerprinter::new(&evaluator, None, None).unwrap();
        assert_ne!(
            fingerprint(&plain, &evaluator, Value::Int(0)),
            fingerprint(&plain, &evaluator, Value::Int(2))
        );
    }

    #[test]
    fn counts_a_state_and_its_permutations_once() {
        let body = "CONSTANT P\nPerms == Permutations(P)";
        let evaluator = evaluator(body, "CONSTANT P = {p1, p2, p3}\nSYMMETRY Perms");
        let fingerprinter =
            Fingerprinter::new(&evaluator, None, Some(Symbol::intern("Perms"))).unwrap();
        let of = |items: &[&str]| {
            let value = Value::tuple(items.iter().map(|name| model(name)).collect());
            fingerprint(&fingerprinter, &evaluator, value)
        };
        assert_eq!(of(&["p1", "p2"]), of(&["p2", "p3"]));
        assert_eq!(of(&["p1", "p1"]), of(&["p3", "p3"]));
        assert_ne!(of(&["p1", "p2"]), of(&["p1", "p1"]));
        // Inside sets and functions too.
        let set = |names: &[&str]| {
            let value = Value::set(names.iter().map(|name| model(name)).collect()).unwrap();
            fingerprint(&fingerprinter, &evaluator, value)
        };
        assert_eq!(set(&["p1"]), set(&["p3"]));
        assert_ne!(set(&["p1"]), set(&["p1", "p2"]));
    }

    #[test]
    fn closes_the_permutations_under_composition() {
        let body = "CONSTANTS a, b, c\nRotate == {(a :> b) @@ (b :> c) @@ (c :> a)}";
        let evaluator = evaluator(body, "CONSTANTS a = a\nb = b\nc = c\nSYMMETRY Rotate");
        let group = symmetry_group(&evaluator, Symbol::intern("Rotate")).unwrap();
        // The rotation and its inverse; the identity is left out.
        assert_eq!(group.len(), 2);
        let Err(error) = symmetry_group(&evaluator, Symbol::intern("Missing")) else {
            panic!("an undefined symmetry is an error")
        };
        assert!(error.message.contains("is not defined"), "{}", error.message);
    }
}
