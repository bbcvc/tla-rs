//! Binds the constants of a specification to the values a model configuration gives them, as
//! tla-ts `environment.ts` does.
//!
//! `N = value` assigns a declared constant, or overrides a definition with a value. `N <- Def`
//! replaces a declared constant or a definition with another definition of the root module.

use tla_parser::{ConfigError, ConfigValue, ModelConfig};
use tla_resolve::{DefId, RootName, Spec};
use tla_value::{Symbol, Value};

use crate::ConstBinding;

/// What the model configuration sets.
pub struct Model {
    /// The binding of each declared constant, by [`tla_resolve::ConstId`].
    pub constants: Vec<ConstBinding>,
    /// Definitions the configuration overrides with a value or another definition.
    pub overrides: Vec<(DefId, ConstBinding)>,
}

fn error(message: impl Into<String>) -> ConfigError {
    ConfigError { message: message.into() }
}

/// The value a configuration writes. A bare identifier is a model value.
pub fn config_value(value: &ConfigValue) -> Result<Value, ConfigError> {
    Ok(match value {
        ConfigValue::Int(number) => Value::Int(i32::try_from(*number).map_err(|_| {
            error(format!("The number {number} in the configuration is too large."))
        })?),
        ConfigValue::Str(text) => Value::Str(*text),
        ConfigValue::Bool(value) => Value::Bool(*value),
        ConfigValue::ModelValue(name) => Value::Model(*name),
        ConfigValue::Set(elements) => {
            let elements = elements.iter().map(config_value).collect::<Result<Vec<_>, _>>()?;
            Value::set(elements).map_err(|failure| error(failure.0))?
        }
    })
}

fn not_in_spec(name: Symbol) -> ConfigError {
    error(format!(
        "In the configuration file, the identifier {name} does not appear in the specification."
    ))
}

fn arity(spec: &Spec, name: RootName) -> usize {
    match name {
        RootName::Const(id) => spec.constants[id.index()].arity,
        RootName::Def(def) => spec.def(def).params.len(),
        RootName::Var(_) => 0,
    }
}

/// Binds every constant of `spec` from `config`.
pub fn bind_model(spec: &Spec, config: &ModelConfig) -> Result<Model, ConfigError> {
    let mut constants: Vec<Option<ConstBinding>> = vec![None; spec.constants.len()];
    let mut overrides = Vec::new();
    let mut bind =
        |name: Symbol, binding: ConstBinding, constants: &mut Vec<Option<ConstBinding>>| {
            match spec.lookup(name.as_str()) {
                Some(RootName::Const(id)) => constants[id.index()] = Some(binding),
                Some(RootName::Def(def)) => overrides.push((def, binding)),
                Some(RootName::Var(_)) | None => return Err(not_in_spec(name)),
            }
            Ok(())
        };
    for assignment in &config.constants {
        if assignment.module.is_some() || !assignment.args.is_empty() {
            return Err(error(format!(
                "Assigning {} in a module or with arguments is not supported yet.",
                assignment.name
            )));
        }
        bind(
            assignment.name,
            ConstBinding::Value(config_value(&assignment.value)?),
            &mut constants,
        )?;
    }
    for substitution in &config.substitutions {
        if substitution.module.is_some() {
            return Err(error(format!(
                "Substituting {} in a module is not supported yet.",
                substitution.name
            )));
        }
        let (name, target) = (substitution.name, substitution.target);
        let Some(replaced) =
            spec.lookup(name.as_str()).filter(|replaced| !matches!(replaced, RootName::Var(_)))
        else {
            return Err(not_in_spec(name));
        };
        if config.substitutions.iter().any(|other| other.name == target) {
            return Err(error(format!(
                "In the configuration file, the identifier {target} appears\non the right-hand side of a <- after already appearing on the\nleft-hand side of one."
            )));
        }
        let Some(RootName::Def(definition)) = spec.lookup(target.as_str()) else {
            return Err(error(format!(
                "The configuration file substitutes for {name} with the undefined identifier {target}."
            )));
        };
        if spec.def(definition).params.len() != arity(spec, replaced) {
            return Err(error(format!(
                "The configuration file substitutes for {name} with {target} of different number of arguments."
            )));
        }
        bind(name, ConstBinding::Def(definition), &mut constants)?;
    }
    let constants = constants
        .into_iter()
        .zip(&spec.constants)
        .map(|(binding, declaration)| {
            binding.ok_or_else(|| {
                error(format!(
                    "The constant parameter {} is not assigned a value by the configuration file.",
                    declaration.name
                ))
            })
        })
        .collect::<Result<_, _>>()?;
    Ok(Model { constants, overrides })
}

#[cfg(test)]
mod tests {
    use tla_parser::parse_config;
    use tla_resolve::{RootName, Spec, resolve};

    use super::bind_model;
    use crate::{ConstBinding, Evaluator};

    fn spec(source: &str) -> Spec {
        resolve(source, &mut |_: &str| None).unwrap()
    }

    const SPEC: &str =
        "---- MODULE M ----\nCONSTANTS N, Procs, F(_)\nDouble(x) == x\nLimit == 3\n====\n";

    #[test]
    fn binds_values_model_values_and_substitutions() {
        let spec = spec(SPEC);
        let config =
            parse_config("CONSTANTS N = 3 Procs = {p1, p2} F <- Double Limit = 5").unwrap();
        let model = bind_model(&spec, &config).unwrap();
        let formatted: Vec<String> = model
            .constants
            .iter()
            .map(|binding| match binding {
                ConstBinding::Value(value) => value.to_string(),
                ConstBinding::Def(def) => spec.def(*def).name.to_string(),
            })
            .collect();
        assert_eq!(formatted, ["3", "{p1, p2}", "Double"]);
        let Some(RootName::Def(limit)) = spec.lookup("Limit") else { panic!() };
        assert!(matches!(&model.overrides[..], [(def, ConstBinding::Value(_))] if *def == limit));
    }

    #[test]
    fn overrides_definitions_with_values_and_definitions() {
        let spec = std::sync::Arc::new(spec(
            "---- MODULE M ----\nLimit == {1}\nOther(x) == {x, 2}\nPick(x) == {x}\nBoth == Limit \\cup Pick(3)\n====\n",
        ));
        let model =
            bind_model(&spec, &parse_config("CONSTANTS Limit = {a} Pick <- Other").unwrap())
                .unwrap();
        let Some(RootName::Def(both)) = spec.lookup("Both") else { panic!() };
        let evaluator = Evaluator::new(spec, model.constants).with_overrides(model.overrides);
        assert_eq!(evaluator.eval_def(both, None).unwrap().to_string(), "{a, 2, 3}");
    }

    #[test]
    fn reports_configuration_errors_like_tlc() {
        let spec = spec(SPEC);
        let message =
            |config: &str| bind_model(&spec, &parse_config(config).unwrap()).err().unwrap().message;
        assert_eq!(
            message("CONSTANTS Procs = {} F <- Double"),
            "The constant parameter N is not assigned a value by the configuration file."
        );
        assert_eq!(
            message("CONSTANTS N = 1 Procs = {} F <- Limit"),
            "The configuration file substitutes for F with Limit of different number of arguments."
        );
        assert_eq!(
            message("CONSTANTS N = 1 Procs = {} F <- Nowhere"),
            "The configuration file substitutes for F with the undefined identifier Nowhere."
        );
        assert_eq!(
            message("CONSTANTS M = 1"),
            "In the configuration file, the identifier M does not appear in the specification."
        );
    }
}
