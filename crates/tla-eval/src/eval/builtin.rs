//! The operators TLA+ defines itself, and the checks TLC makes of their operands.

use tla_resolve::{Builtin, Expr};
use tla_value::{LazySet, Value, bail};

use super::{At, TEMPORAL_ERROR};
use crate::env::Env;
use crate::{Evaluator, Result};

impl Evaluator {
    /// Applies a built-in operator to argument expressions.
    #[inline(never)]
    pub(super) fn builtin(
        &self,
        op: Builtin,
        args: &[Expr],
        expr: &Expr,
        env: &mut Env<'_>,
    ) -> Result<Value> {
        let unsupported = |message: &str| Err(self.error(env, expr, message));
        match op {
            Builtin::And => self.junction(true, args, expr, env),
            Builtin::Or => self.junction(false, args, expr, env),
            Builtin::Implies => {
                if !self.boolean_operand(&args[0], "the left side of =>", env)? {
                    return Ok(Value::TRUE);
                }
                Ok(Value::Bool(self.boolean_operand(&args[1], "the right side of =>", env)?))
            }
            Builtin::Prime => self.prime(&args[0], expr, env),
            Builtin::Unchanged => self.unchanged(&args[0], expr, env).map(Value::Bool),
            Builtin::Enabled => self.is_enabled(&args[0], expr, env).map(Value::Bool),
            Builtin::Always | Builtin::Eventually => self.fail_at(env, expr, TEMPORAL_ERROR),
            Builtin::LeadsTo => {
                unsupported("TLC cannot evaluate a temporal formula such as ~> in a state")
            }
            Builtin::PlusArrow => {
                unsupported("TLC cannot evaluate a temporal formula such as -+-> in a state")
            }
            Builtin::Cdot => unsupported(
                "The current version of TLC does not support action composition.  An incomplete implementation can be enabled via the tlc2.tool.impl.Tool.cdot=true java property.",
            ),
            _ => {
                let values = self.eval_all(args, env)?;
                match (op, values.first()) {
                    (Builtin::Domain, Some(value)) if !value.is_function() => {
                        let message = format!(
                            "Attempted to apply the operator DOMAIN to a non-function\n({})\n{}",
                            describe(value),
                            self.range(env, expr)
                        );
                        Err(self.error(env, expr, message))
                    }
                    (Builtin::SubsetEq, Some(value)) if !value.is_set() || is_overridden(value) => {
                        let message = format!(
                            "Attempted to evaluate an expression of form S \\subseteq T, but S was not enumerable.\n{}",
                            self.range(env, expr)
                        );
                        Err(self.error(env, expr, message))
                    }
                    _ => self.apply_builtin(op, &values).at(self, env, expr),
                }
            }
        }
    }

    fn boolean_operand(
        &self,
        operand: &Expr,
        description: &str,
        env: &mut Env<'_>,
    ) -> Result<bool> {
        match self.eval(operand, env)? {
            Value::Bool(value) => Ok(value),
            value => {
                let message = format!("Expected {description} to be a boolean but found {value}");
                Err(self.error(env, operand, message))
            }
        }
    }

    /// Applies a built-in operator to values, as when it is passed as an argument, such as
    /// `\cup` in `F(\cup)`.
    pub(crate) fn apply_builtin(
        &self,
        builtin: Builtin,
        args: &[Value],
    ) -> tla_value::Result<Value> {
        if args.len() != builtin.arity() {
            bail!(
                "The built-in operator {builtin:?} takes {} arguments, but is applied to {}.",
                builtin.arity(),
                args.len()
            );
        }
        Ok(match builtin {
            Builtin::Boolean => Value::set(vec![Value::FALSE, Value::TRUE])?,
            Builtin::String => Value::lazy(LazySet::String),
            Builtin::And => Value::Bool(boolean(&args[0], "/\\")? && boolean(&args[1], "/\\")?),
            Builtin::Or => Value::Bool(boolean(&args[0], "\\/")? || boolean(&args[1], "\\/")?),
            Builtin::Implies => Value::Bool(!boolean(&args[0], "=>")? || boolean(&args[1], "=>")?),
            Builtin::Equiv => Value::Bool(boolean(&args[0], "<=>")? == boolean(&args[1], "<=>")?),
            Builtin::Not => Value::Bool(!boolean(&args[0], "~")?),
            Builtin::Eq => Value::Bool(args[0].equals(&args[1])?),
            Builtin::Neq => Value::Bool(!args[0].equals(&args[1])?),
            Builtin::In => Value::Bool(args[1].contains(&args[0])?),
            Builtin::NotIn => Value::Bool(!args[1].contains(&args[0])?),
            Builtin::SubsetEq => {
                if !args[0].is_set() {
                    bail!("\\subseteq expects a set but received {}", args[0]);
                }
                Value::Bool(args[0].is_subset_of(&args[1])?)
            }
            Builtin::Cup => args[0].cup(&args[1])?,
            Builtin::Cap => args[0].cap(&args[1])?,
            Builtin::SetMinus => args[0].minus(&args[1])?,
            Builtin::Powerset => Value::lazy(LazySet::Subset(args[0].clone())),
            Builtin::Union => {
                if !args[0].is_set() {
                    bail!("UNION expects a set but received {}", args[0]);
                }
                args[0].union()?
            }
            Builtin::Domain => {
                if !args[0].is_function() {
                    bail!("DOMAIN expects a function but received {}", args[0]);
                }
                args[0].domain()?
            }
            Builtin::Prime
            | Builtin::Unchanged
            | Builtin::Enabled
            | Builtin::Always
            | Builtin::Eventually
            | Builtin::LeadsTo
            | Builtin::PlusArrow
            | Builtin::Cdot => bail!("The operator {builtin:?} can't be applied to values."),
        })
    }
}

fn boolean(value: &Value, operator: &str) -> tla_value::Result<bool> {
    match value {
        Value::Bool(value) => Ok(*value),
        _ => bail!("{operator} expects a boolean but received {value}"),
    }
}

/// Whether TLC implements the set in Java, as a set it can't enumerate.
pub(super) fn is_overridden(value: &Value) -> bool {
    matches!(
        value,
        Value::Lazy(set)
            if matches!(**set, LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any | LazySet::Seq(_))
    )
}

/// What kind of value this is, as TLC describes it in errors.
pub(crate) fn describe(value: &Value) -> &'static str {
    match value {
        Value::Bool(_) => "a Boolean value",
        Value::Int(_) => "an integer",
        Value::Str(_) => "a string",
        Value::Model(_) => "a model value",
        Value::Set(_) | Value::MixedSet(_) => "a set of the form {e1, ... ,eN}",
        Value::Interval(..) => "a set of the form i..j",
        Value::Tuple(_) => "a tuple",
        Value::Func(func) if func.keys.iter().all(|key| matches!(key, Value::Str(_))) => "a record",
        Value::Func(_) => "a function  of the form (d1 :> e1 @@ ... @@ dN :> eN)",
        Value::LazyFunc(_) => "a function of the form  [x \\in S |-> expr]",
        Value::Lazy(set) => match **set {
            LazySet::Subset(_) => "a set of the form SUBSET S",
            LazySet::FuncSet { .. } => "a set of the form [S -> T]",
            LazySet::RecordSet(_) => "a set of the form [d1 : S1, ... , dN : SN]",
            LazySet::Product(_) => "a cartesian product",
            LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::String | LazySet::Any => {
                "a special set constant"
            }
            LazySet::Cup(..) => "a set of the form S \\cup T",
            LazySet::Cap(..) => "a set of the form S \\cap T",
            LazySet::Minus(..) => "a set of the form S \\ T",
            LazySet::Filtered { .. } => "a set of the form {x \\in S : expr}",
            LazySet::Union(_) => "a set of the form UNION  S",
        },
    }
}
