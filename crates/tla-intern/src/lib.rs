//! Process-wide symbol interner.
//!
//! Every identifier, operator name, and string literal becomes a [`Symbol`], a 32-bit handle
//! that compares and hashes in O(1). The interner is shared by all threads and lives for the
//! whole process, so [`Symbol::as_str`] returns a `&'static str`.

use std::fmt;
use std::sync::OnceLock;

use lasso::{Spur, ThreadedRodeo};

fn interner() -> &'static ThreadedRodeo {
    static INTERNER: OnceLock<ThreadedRodeo> = OnceLock::new();
    INTERNER.get_or_init(ThreadedRodeo::new)
}

/// An interned string.
///
/// `Ord` follows the order in which texts were first interned, not their lexical order.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(Spur);

impl Symbol {
    pub fn intern(text: &str) -> Self {
        Self(interner().get_or_intern(text))
    }

    /// Returns the symbol for `text` if it was interned before, without interning it.
    pub fn get(text: &str) -> Option<Self> {
        interner().get(text).map(Self)
    }

    pub fn as_str(self) -> &'static str {
        interner().resolve(&self.0)
    }
}

impl From<&str> for Symbol {
    fn from(text: &str) -> Self {
        Self::intern(text)
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), formatter)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::Symbol;

    #[test]
    fn interning_is_idempotent() {
        let first = Symbol::intern("participant");
        assert_eq!(first, Symbol::intern("participant"));
        assert_eq!(first.as_str(), "participant");
        assert_ne!(first, Symbol::intern("coordinator"));
    }

    #[test]
    fn order_follows_first_intern() {
        let later = Symbol::intern("order-test-b");
        let earlier = Symbol::intern("order-test-a");
        assert!(later < earlier);
        assert_eq!(Symbol::get("order-test-a"), Some(earlier));
        assert_eq!(Symbol::get("order-test-never"), None);
    }
}
