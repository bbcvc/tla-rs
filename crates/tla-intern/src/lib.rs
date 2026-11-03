//! Process-wide symbol interner.
//!
//! Every identifier, operator name, and string literal becomes a [`Symbol`], a 32-bit handle
//! that compares and hashes in O(1). The interner is shared by all threads and lives for the
//! whole process, so [`Symbol::as_str`] returns a `&'static str`.
//!
//! Symbols are ordered as TLC orders strings and model values: by when TLC first interns their
//! text. [`set_order`] gives the texts TLC interns before it checks a spec, in order, and every
//! other symbol comes after them in the order this process interned it.

use std::cmp::Ordering;
use std::fmt;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicPtr, Ordering as AtomicOrdering};

use lasso::{Key, Spur, ThreadedRodeo};

fn interner() -> &'static ThreadedRodeo {
    static INTERNER: OnceLock<ThreadedRodeo> = OnceLock::new();
    INTERNER.get_or_init(ThreadedRodeo::new)
}

/// The key each symbol sorts by, by intern index: its rank from 1 for a ranked symbol, and
/// `ranked + 1 + index` for any other, so that ranked symbols come first and the others keep the
/// order of interning. A symbol interned after the table was built has the second form.
struct Ranks {
    keys: Box<[u32]>,
    ranked: u32,
}

impl Ranks {
    fn key(&self, symbol: Symbol) -> u32 {
        let index = symbol.0.into_usize();
        match self.keys.get(index) {
            Some(&key) => key,
            None => self.ranked + 1 + index as u32,
        }
    }
}

/// The ranks [`set_order`] last set, or null. A replaced table is leaked rather than freed,
/// since another thread may still read it; a process sets an order once per spec.
static RANKS: AtomicPtr<Ranks> = AtomicPtr::new(std::ptr::null_mut());

/// Orders the symbols of `texts` first, in the order given, ahead of every other symbol, which
/// keeps the order of interning. A text given twice keeps its first place. It replaces the order
/// of an earlier call, so it belongs before a spec's values are built, as sorted sets and
/// records depend on it.
pub fn set_order<'a>(texts: impl IntoIterator<Item = &'a str>) {
    let mut ranks: Vec<u32> = Vec::new();
    let mut ranked = 0;
    for text in texts {
        let index = Symbol::intern(text).0.into_usize();
        if ranks.len() <= index {
            ranks.resize(index + 1, 0);
        }
        if ranks[index] == 0 {
            ranked += 1;
            ranks[index] = ranked;
        }
    }
    ranks.resize(interner().len().max(ranks.len()), 0);
    for (index, key) in ranks.iter_mut().enumerate() {
        if *key == 0 {
            *key = ranked + 1 + index as u32;
        }
    }
    let table = Box::into_raw(Box::new(Ranks { keys: ranks.into(), ranked }));
    RANKS.store(table, AtomicOrdering::Release);
}

/// The texts [`Symbol::as_str`] has resolved, by intern index, in chunks that double in size:
/// chunk `c` holds the indexes from `FIRST_CHUNK * (2^c - 1)`.
static TEXTS: [OnceLock<Box<[OnceLock<Text>]>>; 40] = [const { OnceLock::new() }; 40];

/// A text, and what [`Symbol::model_type`] tells of it.
struct Text {
    text: &'static str,
    model_type: Option<char>,
}

const FIRST_CHUNK: usize = 1024;

/// The table [`set_order`] last published.
fn ranks() -> Option<&'static Ranks> {
    // SAFETY: a published table is never freed.
    unsafe { RANKS.load(AtomicOrdering::Acquire).as_ref() }
}

/// An interned string.
///
/// `Ord` is TLC's order of strings: the order [`set_order`] gives, then the order in which texts
/// were first interned. `Eq` and `Hash` compare the texts.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(Spur);

impl Ord for Symbol {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.0 == other.0 {
            return Ordering::Equal;
        }
        match ranks() {
            Some(ranks) => ranks.key(*self).cmp(&ranks.key(*other)),
            None => self.0.into_usize().cmp(&other.0.into_usize()),
        }
    }
}

impl PartialOrd for Symbol {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Symbol {
    pub fn intern(text: &str) -> Self {
        Self(interner().get_or_intern(text))
    }

    /// Returns the symbol for `text` if it was interned before, without interning it.
    pub fn get(text: &str) -> Option<Self> {
        interner().get(text).map(Self)
    }

    pub fn as_str(self) -> &'static str {
        self.text().text
    }

    /// The type TLC gives a model value of this name: `T` for a name of the form `T_rest`.
    pub fn model_type(self) -> Option<char> {
        self.text().model_type
    }

    fn text(self) -> &'static Text {
        // Resolving a symbol through the shared interner takes a lock, and a text never changes
        // once interned, so each text is resolved once into a table without locks.
        let index = self.0.into_usize();
        let chunk = (usize::BITS - (index / FIRST_CHUNK + 1).leading_zeros() - 1) as usize;
        let start = FIRST_CHUNK * ((1 << chunk) - 1);
        let texts = TEXTS[chunk]
            .get_or_init(|| (0..FIRST_CHUNK << chunk).map(|_| OnceLock::new()).collect());
        texts[index - start].get_or_init(|| {
            let text = interner().resolve(&self.0);
            let mut chars = text.chars();
            let model_type =
                chars.next().filter(|_| chars.next() == Some('_') && chars.next().is_some());
            Text { text, model_type }
        })
    }

    /// The number TLC's interner gives the text, from 1: its place in the order [`set_order`]
    /// last gave, or after those for a text not in it, in the order this process interned it.
    /// TLC's fingerprint of a model value includes it.
    pub fn tlc_number(self) -> u32 {
        match ranks() {
            Some(ranks) => ranks.key(self),
            None => self.0.into_usize() as u32 + 1,
        }
    }

    /// The symbol's place in the order [`set_order`] last gave, from 0, if it has one.
    pub fn rank(self) -> Option<u32> {
        let ranks = ranks()?;
        let key = ranks.key(self);
        (key <= ranks.ranked).then(|| key - 1)
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
    fn tells_the_type_of_a_model_value_name() {
        let model_type = |text: &str| Symbol::intern(text).model_type();
        assert_eq!(model_type("T_a"), Some('T'));
        assert_eq!(model_type("a"), None);
        assert_eq!(model_type("T_"), None);
        assert_eq!(model_type("ab_c"), None);
    }

    #[test]
    fn resolves_texts_across_chunks() {
        let symbols: Vec<(Symbol, String)> = (0..5000)
            .map(|index| {
                let text = format!("chunk-test-{index}");
                (Symbol::intern(&text), text)
            })
            .collect();
        for (symbol, text) in symbols.iter().rev() {
            assert_eq!(symbol.as_str(), text);
        }
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
