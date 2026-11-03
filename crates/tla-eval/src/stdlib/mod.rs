//! Native implementations of TLC's standard modules.

use crate::Native;

/// The native implementation of `name` in standard module `module`. TLC overrides the arithmetic
/// of Naturals with that of Integers when the spec loads Integers anywhere.
pub(crate) fn lookup(module: &str, name: &str, uses_integers: bool) -> Option<Native> {
    let _ = (module, name, uses_integers);
    None
}
