//! TLA+ values, with TLC's semantics for equality, ordering, membership, and printing.
//!
//! Every value has one canonical form, so two equal finite values have the same structure and
//! the same fingerprint: a function whose domain is `1..n` is always a [`Value::Tuple`], a set
//! is sorted and free of duplicates, and a record is a function whose keys are strings. Sets
//! TLC doesn't enumerate eagerly, such as `SUBSET S` or `Nat`, stay lazy until something needs
//! their elements.
//!
//! [`Value`] doesn't implement `Eq` or `Hash`, because equality in TLA+ crosses representations
//! (`1..3 = {1, 2, 3}`) and can fail (`1 = "a"` is an error in TLC). Use [`Value::equals`],
//! [`Value::compare`], and [`Value::fingerprint`] instead.

mod combinations;
mod fingerprint;
mod format;
mod func;
mod order;
mod permute;
mod set;
mod stream;

use std::fmt;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, OnceLock};

pub use combinations::{Combinations, Enumeration};
pub use func::Key;
pub use tla_intern::{Symbol, set_order};

/// An evaluation error, worded like TLC's where TLC reports the same problem.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("{0}")]
pub struct Error(pub String);

pub type Result<T> = std::result::Result<T, Error>;

/// Fails with a message formatted like `format!`.
#[macro_export]
macro_rules! bail {
    ($($arg:tt)*) => {
        return Err($crate::Error(format!($($arg)*)))
    };
}

/// Fails like [`bail!`], unless printing one of the values in brackets fails first, as TLC's
/// message fails when it normalizes a set enumeration it can't sort.
macro_rules! fail {
    ([$($value:expr),*], $($arg:tt)*) => {{
        $($value.check_printable()?;)*
        $crate::bail!($($arg)*)
    }};
}
pub(crate) use fail;

/// A test a lazily filtered set applies to each element.
pub type Predicate = Arc<dyn Fn(&Value) -> Result<bool> + Send + Sync>;

/// The body of a function TLC doesn't enumerate, applied to each argument.
pub type Mapping = Arc<dyn Fn(&Value) -> Result<Value> + Send + Sync>;

#[derive(Clone)]
pub enum Value {
    Bool(bool),
    /// TLC's integers are 32-bit, and arithmetic that leaves that range is an error.
    Int(i32),
    Str(Symbol),
    /// An uninterpreted constant from the model configuration, equal only to itself. A name of
    /// the form `T_name` gives it type `T`, and TLC refuses to compare it with a value of another
    /// type.
    Model(Symbol),
    /// A finite set, sorted by [`Value::compare`] and free of duplicates.
    Set(Arc<[Value]>),
    /// A set enumeration whose elements TLC can't sort, such as `{1, "a"}`. TLC checks
    /// membership in one element by element, and fails when it has to sort it.
    MixedSet(Arc<[Value]>),
    /// A function with domain `1..n`: a tuple or sequence, including the empty one.
    Tuple(Arc<[Value]>),
    /// Any other finite function, including records.
    Func(Arc<Func>),
    /// `low..high`, empty when `low > high`.
    Interval(i32, i32),
    Lazy(LazySetRef),
    /// A function TLC applies on demand rather than enumerate, such as `[n \in Nat |-> n + 1]`.
    LazyFunc(Arc<LazyFunc>),
}

/// A finite function other than a tuple: keys sorted by [`Value::compare`], with the value of
/// each key at the same index.
///
/// A record, or a function with string keys that `@@` builds, also remembers the order the spec
/// wrote its keys in when that isn't the sorted order. TLC prints that order until it normalizes
/// the value, which it does to compare or fingerprint it. Equality, ordering, and fingerprints
/// never depend on it.
#[derive(Clone)]
pub struct Func {
    pub keys: Box<[Value]>,
    pub values: Box<[Value]>,
    pub(crate) written: Option<Box<func::WrittenOrder>>,
}

#[derive(Clone)]
pub struct LazyFunc {
    pub domain: Value,
    pub apply: Mapping,
    /// What the function was built from, for an evaluator that reads it back, as TLC walks the
    /// body of a function of actions that an action applies. `None` for a function the value
    /// system builds itself.
    pub source: Option<Arc<dyn std::any::Any + Send + Sync>>,
}

/// A shared lazy set, with its elements once enumerated, which TLC keeps, as tla-ts's
/// `toFiniteSet` does, so that a set enumerated again, such as one a constant definition holds,
/// isn't recomputed.
#[derive(Clone)]
pub struct LazySetRef(Arc<LazySetCell>);

struct LazySetCell {
    set: LazySet,
    elements: OnceLock<Arc<[Value]>>,
    /// Whether TLC has cached the set's elements, after which it streams them in its order
    /// rather than streaming the sets it combines. See [`Value::streamed_elements`].
    cached: AtomicBool,
}

impl LazySetRef {
    /// The elements, once enumerated.
    pub(crate) fn elements(&self) -> &OnceLock<Arc<[Value]>> {
        &self.0.elements
    }

    /// Marks the set cached, as TLC caches it.
    pub(crate) fn cache(&self) {
        if !self.is_cached() {
            self.0.cached.store(true, Ordering::Relaxed);
        }
    }

    pub(crate) fn is_cached(&self) -> bool {
        self.0.cached.load(Ordering::Relaxed)
    }
}

impl std::ops::Deref for LazySetRef {
    type Target = LazySet;

    fn deref(&self) -> &LazySet {
        &self.0.set
    }
}

/// A set TLC represents symbolically.
#[derive(Clone)]
pub enum LazySet {
    /// `SUBSET base`.
    Subset(Value),
    /// `[domain -> range]`.
    FuncSet {
        domain: Value,
        range: Value,
    },
    /// `[a : S, b : T]`, with fields sorted by name.
    RecordSet(Box<[(Symbol, Value)]>),
    /// `S \X T \X ...`.
    Product(Box<[Value]>),
    /// `Seq(S)`.
    Seq(Value),
    Nat,
    Int,
    String,
    /// TLC's `Any`, which contains every value.
    Any,
    Cup(Value, Value),
    Cap(Value, Value),
    Minus(Value, Value),
    /// `{x \in base : test}` over a base TLC can't enumerate.
    Filtered {
        base: Value,
        test: Predicate,
    },
    /// `UNION base` when some element of `base` isn't enumerable.
    Union(Value),
}

impl Value {
    pub const TRUE: Self = Self::Bool(true);
    pub const FALSE: Self = Self::Bool(false);

    pub fn str(text: &str) -> Self {
        Self::Str(Symbol::intern(text))
    }

    pub fn empty_set() -> Self {
        Self::Set(Arc::from([]))
    }

    pub fn empty_tuple() -> Self {
        Self::Tuple(Arc::from([]))
    }

    pub fn tuple(items: Vec<Value>) -> Self {
        Self::Tuple(items.into())
    }

    pub fn lazy(set: LazySet) -> Self {
        stream::note_lazy(&set);
        let cell = LazySetCell { set, elements: OnceLock::new(), cached: AtomicBool::new(false) };
        Self::Lazy(LazySetRef(Arc::new(cell)))
    }

    /// The model value `name`, typed if its name is `T_rest`.
    pub fn model(name: &str) -> Self {
        Self::Model(Symbol::intern(name))
    }

    /// What kind of value this is, as TLC names it in errors.
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Bool(_) => "boolean",
            Self::Int(_) => "integer",
            Self::Str(_) => "string",
            Self::Model(_) => "model value",
            Self::Set(_) | Self::MixedSet(_) | Self::Interval(..) | Self::Lazy(_) => "set",
            Self::Tuple(_) => "tuple",
            Self::Func(func) if func.keys.iter().all(|key| matches!(key, Self::Str(_))) => "record",
            Self::Func(_) | Self::LazyFunc(_) => "function",
        }
    }

    pub fn is_set(&self) -> bool {
        matches!(self, Self::Set(_) | Self::MixedSet(_) | Self::Interval(..) | Self::Lazy(_))
    }

    pub fn is_function(&self) -> bool {
        matches!(self, Self::Tuple(_) | Self::Func(_) | Self::LazyFunc(_))
    }

    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(value) => Some(*value),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<i32> {
        match self {
            Self::Int(value) => Some(*value),
            _ => None,
        }
    }
}

/// The type letter of a model value named `T_rest`.
pub(crate) fn model_type(name: Symbol) -> Option<char> {
    let mut chars = name.as_str().chars();
    let first = chars.next()?;
    (chars.next() == Some('_') && chars.next().is_some()).then_some(first)
}

impl fmt::Debug for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, formatter)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn types_model_values_by_prefix() {
        assert_eq!(model_type(Symbol::intern("A_x")), Some('A'));
        assert_eq!(model_type(Symbol::intern("ax")), None);
        assert_eq!(model_type(Symbol::intern("A_")), None);
    }
}
