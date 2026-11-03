//! Binds the constants of a specification to the values a model configuration gives them.

use tla_parser::ModelConfig;
use tla_resolve::Spec;

use crate::{ConstBinding, Result};

/// The binding of each constant of `spec`, by [`tla_resolve::ConstId`].
pub fn bind_constants(spec: &Spec, config: &ModelConfig) -> Result<Vec<ConstBinding>> {
    let _ = (spec, config);
    todo!("bind constants")
}
