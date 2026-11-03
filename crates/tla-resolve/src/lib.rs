//! Resolves the names in a TLA+ specification.

mod stdlib;

/// Whether TLC bundles a module of this name. A loader shouldn't supply one from a library
/// directory, since TLC finds its own first.
pub fn is_standard_module(name: &str) -> bool {
    stdlib::standard_module(name).is_some()
}
