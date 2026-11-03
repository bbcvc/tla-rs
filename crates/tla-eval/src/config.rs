//! Binds the constants of a specification to the values a model configuration gives them, as
//! tla-ts `environment.ts` does.
//!
//! `N = value` assigns a declared constant, or overrides a definition with a value. `F(1) = 2`
//! defines an operator by a table of its values. `N <- Def` replaces a declared constant or a
//! definition with another definition of the root module. `[M]` applies an entry to the
//! definition of that name in module `M`, which every instance of `M` shares.

use std::fmt;
use std::sync::Arc;

use tla_parser::{ConfigError, ConfigValue, ModelConfig};
use tla_resolve::{DefId, RootName, Spec};
use tla_value::{LazySet, Symbol, Value, bail};

use crate::ConstBinding;

/// What the model configuration sets.
pub struct Model {
    /// The binding of each declared constant, by [`tla_resolve::ConstId`].
    pub constants: Vec<ConstBinding>,
    /// Definitions the configuration overrides, in order: a later entry wins.
    pub overrides: Vec<(DefId, ConstBinding)>,
}

/// An operator the configuration defines by its values, as in `F(0) = 1  F(1) = 2`.
pub struct OperatorTable {
    pub rows: Vec<(Vec<Value>, Value)>,
}

impl OperatorTable {
    /// The value of the row whose arguments equal `args`.
    pub fn apply(&self, args: &[Value]) -> tla_value::Result<Value> {
        'rows: for (keys, value) in &self.rows {
            if keys.len() != args.len() {
                bail!("Attempted to apply the operator {self}\nwith wrong number of arguments.");
            }
            for (key, arg) in keys.iter().zip(args) {
                if !key.equals(arg)? {
                    continue 'rows;
                }
            }
            return Ok(value.clone());
        }
        let args = args.iter().map(Value::to_string).collect::<Vec<_>>().join(", ");
        bail!("Attempted to apply operator:\n{self}\nto arguments ({args}), which is undefined.")
    }
}

/// TLC's printing of the table: `{ <0, 1>, <1, 2>}`.
impl fmt::Display for OperatorTable {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let rows = self.rows.iter().map(|(keys, value)| {
            let cells = keys.iter().chain([value]).map(Value::to_string).collect::<Vec<_>>();
            format!("<{}>", cells.join(", "))
        });
        write!(formatter, "{{ {}}}", rows.collect::<Vec<_>>().join(", "))
    }
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

fn arity(spec: &Spec, name: RootName) -> usize {
    match name {
        RootName::Const(id) => spec.constants[id.index()].arity,
        RootName::Def(def) => spec.def(def).params.len(),
        RootName::Var(_) => 0,
    }
}

/// What an entry for `name`, scoped to `module` if it has one, replaces. TLC ignores an entry for
/// a name the specification doesn't have, and a scoped entry for the root module or a declared
/// constant.
fn targets(spec: &Spec, name: Symbol, module: Option<Symbol>) -> Option<RootName> {
    let Some(module) = module else {
        return spec.lookup(name.as_str()).filter(|found| !matches!(found, RootName::Var(_)));
    };
    let is_declared = spec.constants.iter().any(|constant| constant.name == name);
    if module == spec.modules[0].name || is_declared {
        return None;
    }
    let module = spec.modules.iter().position(|info| info.name == module)?;
    let index = spec
        .defs
        .iter()
        .position(|def| def.name == name && def.module.index() == module && def.depth == 0)?;
    Some(RootName::Def(DefId(index as u32)))
}

/// What `N <- target` replaces `N` with.
fn substitute(
    spec: &Spec,
    name: Symbol,
    target: Symbol,
    replaced: Option<RootName>,
    constants: &[Option<ConstBinding>],
) -> Result<ConstBinding, ConfigError> {
    let undefined = || {
        error(format!(
            "The configuration file substitutes for {name} with the undefined identifier {target}."
        ))
    };
    match spec.lookup(target.as_str()) {
        Some(RootName::Def(definition)) => {
            let params = spec.def(definition).params.len();
            if replaced.is_some_and(|replaced| params != arity(spec, replaced)) {
                return Err(error(format!(
                    "The configuration file substitutes for {name} with {target} of different number of arguments."
                )));
            }
            Ok(ConstBinding::Def(definition))
        }
        Some(RootName::Const(id)) => constants[id.index()].clone().ok_or_else(undefined),
        Some(RootName::Var(_)) => Err(error(format!(
            "Substituting {name} with the variable {target} is not supported yet."
        ))),
        None => Ok(ConstBinding::Value(match target.as_str() {
            "TRUE" => Value::TRUE,
            "FALSE" => Value::FALSE,
            "BOOLEAN" => Value::set(vec![Value::FALSE, Value::TRUE]).expect("booleans sort"),
            "STRING" => Value::lazy(LazySet::String),
            _ => return Err(undefined()),
        })),
    }
}

/// Binds every constant of `spec` from `config`.
pub fn bind_model(spec: &Spec, config: &ModelConfig) -> Result<Model, ConfigError> {
    let mut constants: Vec<Option<ConstBinding>> = vec![None; spec.constants.len()];
    let mut overrides = Vec::new();
    let mut bind = |target: Option<RootName>,
                    binding: ConstBinding,
                    constants: &mut Vec<Option<ConstBinding>>| match target {
        Some(RootName::Const(id)) => constants[id.index()] = Some(binding),
        Some(RootName::Def(def)) => overrides.push((def, binding)),
        Some(RootName::Var(_)) | None => {}
    };

    for assignment in config.constants.iter().filter(|assignment| assignment.args.is_empty()) {
        let value = config_value(&assignment.value)?;
        let target = targets(spec, assignment.name, assignment.module);
        bind(target, ConstBinding::Value(value), &mut constants);
    }

    let mut tables: Vec<(Option<Symbol>, Symbol, OperatorTable)> = Vec::new();
    for assignment in config.constants.iter().filter(|assignment| !assignment.args.is_empty()) {
        let args = assignment.args.iter().map(config_value).collect::<Result<Vec<_>, _>>()?;
        let value = config_value(&assignment.value)?;
        let key = (assignment.module, assignment.name);
        let index = match tables.iter().position(|(module, name, _)| (*module, *name) == key) {
            Some(index) => index,
            None => {
                tables.push((key.0, key.1, OperatorTable { rows: Vec::new() }));
                tables.len() - 1
            }
        };
        let rows = &mut tables[index].2.rows;
        if rows.first().is_some_and(|(first, _)| first.len() != args.len()) {
            return Err(error(format!(
                "The arity of the operator {} is inconsistent in the configuration file.",
                assignment.name
            )));
        }
        rows.push((args, value));
    }
    for (module, name, table) in tables {
        bind(targets(spec, name, module), ConstBinding::Table(Arc::new(table)), &mut constants);
    }

    for substitution in &config.substitutions {
        let (name, target) = (substitution.name, substitution.target);
        let replaced = targets(spec, name, substitution.module);
        if substitution.module.is_some() && replaced.is_none() {
            continue;
        }
        if substitution.module.is_none() {
            if replaced.is_none() {
                return Err(error(format!(
                    "In the configuration file, the identifier {name} does not appear in the specification."
                )));
            }
            if config.substitutions.iter().any(|other| other.name == target) {
                return Err(error(format!(
                    "In the configuration file, the identifier {target} appears\non the right-hand side of a <- after already appearing on the\nleft-hand side of one."
                )));
            }
        }
        let binding = substitute(spec, name, target, replaced, &constants)?;
        bind(replaced, binding, &mut constants);
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
                ConstBinding::Table(table) => table.to_string(),
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
            message("CONSTANTS N = 1 Procs = {} F <- Double M <- Limit"),
            "In the configuration file, the identifier M does not appear in the specification."
        );
        assert_eq!(
            message("CONSTANTS N = 1 Procs = {} F(0) = 1 F(1, 2) = 3"),
            "The arity of the operator F is inconsistent in the configuration file."
        );
    }

    #[test]
    fn applies_tables_scoped_entries_and_builtin_targets() {
        let root = r#"
---- MODULE M ----
EXTENDS Lib
CONSTANTS F(_), Flag
Small == {7}
Apply(G(_)) == G(1)
Tabled == <<F(0), F(1), Apply(F)>>
Uses == <<Base, Flag>>
Missing == F(5)
====
"#;
        let lib = "---- MODULE Lib ----\nBase == {1}\n====\n";
        let spec = std::sync::Arc::new(
            resolve(root, &mut |name: &str| (name == "Lib").then(|| lib.to_string())).unwrap(),
        );
        // TLC ignores an assignment to a name the specification doesn't have, such as a model
        // value written `n1 = n1`.
        let config = "CONSTANTS n1 = n1 F(0) = 1 F(1) = 2 Flag <- FALSE Base <- [Lib] Small";
        let model = bind_model(&spec, &parse_config(config).unwrap()).unwrap();
        let evaluator =
            Evaluator::new(spec.clone(), model.constants).with_overrides(model.overrides);
        let eval = |name: &str| {
            let Some(RootName::Def(def)) = spec.lookup(name) else { panic!("{name}") };
            evaluator.eval_def(def, None)
        };
        assert_eq!(eval("Tabled").unwrap().to_string(), "<<1, 2, 2>>");
        assert_eq!(eval("Uses").unwrap().to_string(), "<<{7}, FALSE>>");
        assert_eq!(
            eval("Missing").unwrap_err().message,
            "Attempted to apply operator:\n{ <0, 1>, <1, 2>}\nto arguments (5), which is undefined."
        );
    }
}
