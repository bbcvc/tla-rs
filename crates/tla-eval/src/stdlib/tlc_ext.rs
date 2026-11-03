//! TLCExt and `_Possible`, ported from tla-ts `tlc/tlcext-operators.ts`.
//!
//! Natives get their arguments evaluated, so `AssertError` and `PickSuccessor`, which TLC hands
//! unevaluated expressions, fail as unsupported. `TLCDefer` and `TLCCache` evaluate their
//! expression, which TLC defers or caches: their values are TLC's.

use tla_resolve::RootName;
use tla_value::{Symbol, Value};

use super::tlc::{possible_counts, register, set_register, strict_text, tlc_fingerprint};
use super::{Failure, Outcome, arg, java_error, op_arg, sequence_elements};
use crate::native::OperatorKind;
use crate::{Arg, Ctx, Native, Operator};

pub(super) fn lookup(name: &str) -> Option<Native> {
    Some(match name {
        "AssertEq" => native!(assert_eq),
        "AssertError" => unsupported!("AssertError"),
        "TLCGetOrDefault" => native!(tlc_get_or_default),
        "TLCGetAndSet" => native!(tlc_get_and_set),
        "Trace" => native!(trace),
        "CounterExample" => native!(counter_example),
        "ToTrace" => native!(to_trace),
        "TLCModelValue" => native!(tlc_model_value),
        "TLCDefer" => native!(|_: &mut Ctx<'_>, _: &[Arg]| -> Outcome { Ok(Value::TRUE) }),
        "TLCNoOp" | "TLCCache" => {
            native!(|_: &mut Ctx<'_>, args: &[Arg]| -> Outcome { Ok(arg(args, 0)?.clone()) })
        }
        "PickSuccessor" => unsupported!("PickSuccessor"),
        "TLCFP" => native!(tlc_fp),
        "TLCEvalDefinition" => native!(tlc_eval_definition),
        _ => return None,
    })
}

pub(super) fn lookup_possible(name: &str) -> Option<Native> {
    Some(match name {
        "_Track" => native!(track),
        "_Counts" => native!(counts),
        "_CheckName" => native!(check_name),
        "_PrintCounts" => native!(print_counts),
        _ => return None,
    })
}

const TRACE: &str = "public static tlc2.value.impl.TupleValue tlc2.module.TLCExt.getTrace(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel) throws java.io.IOException";

fn assert_eq(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let (left, right) = (arg(args, 0)?, arg(args, 1)?);
    let is_equal = left.equals(right)?;
    if !is_equal {
        let lines = [
            strict_text(&Value::str("Assertion failed"))?,
            strict_text(left)?,
            strict_text(right)?,
        ];
        lines.into_iter().for_each(|line| ctx.runtime().print(line));
    }
    Ok(Value::Bool(is_equal))
}

fn tlc_get_or_default(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    match register(ctx.runtime(), arg(args, 0)?)? {
        Some(value) => Ok(value),
        None => Ok(arg(args, 1)?.clone()),
    }
}

/// `TLCGetAndSet(key, Op, val, defaultVal)`: sets the register to `Op(old, val)` and returns
/// the old value.
fn tlc_get_and_set(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let key = arg(args, 0)?;
    let previous = match register(ctx.runtime(), key)? {
        Some(value) => value,
        None => arg(args, 3)?.clone(),
    };
    let update = op_arg(args, 1)?;
    let value = ctx.call(update, &[previous.clone(), arg(args, 2)?.clone()])?;
    set_register(ctx.runtime(), key, value)?;
    Ok(previous)
}

/// The behavior that leads to the current state, as records of the variables.
fn trace(ctx: &mut Ctx<'_>, _: &[Arg]) -> Outcome {
    let variables = &ctx.evaluator.spec.variables;
    let Some(state) = ctx.state() else {
        let names = variables.iter().map(|variable| variable.name.as_str()).collect::<Vec<_>>();
        let plural = if names.len() > 1 { "s" } else { "" };
        let message = format!(
            "In evaluating TLCExt!Trace, the state is not completely specified yet (variable{plural} {} undefined).",
            names.join(", ")
        );
        return Err(Failure::Eval(java_error(TRACE, &message)));
    };
    let Some(behavior) = ctx.runtime().behavior(state) else {
        fail!("Trace is not supported yet without the model checker");
    };
    let records = behavior.iter().map(|step| {
        let fields = variables.iter().zip(step.iter());
        Value::record(fields.map(|(variable, value)| (variable.name, value.clone())).collect())
    });
    Ok(Value::tuple(records.collect()))
}

fn record(fields: Vec<(&str, Value)>) -> Value {
    Value::record(fields.into_iter().map(|(name, value)| (Symbol::intern(name), value)).collect())
}

fn counter_example(ctx: &mut Ctx<'_>, _: &[Arg]) -> Outcome {
    Ok(ctx.runtime().counter_example().unwrap_or_else(|| {
        record(vec![("action", Value::empty_set()), ("state", Value::empty_set())])
    }))
}

/// `ToTrace(CounterExample)`: the states of a counterexample in order.
fn to_trace(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let counter_example = arg(args, 0)?;
    let keys = Value::set(vec![Value::str("action"), Value::str("state")])?;
    if !counter_example.is_function() || !counter_example.domain()?.equals(&keys)? {
        fail_eval!(
            "The argument of ToTrace should be a CounterExample, but instead it is:\n{counter_example}"
        );
    }
    let mut states = Vec::new();
    for pair in counter_example.apply(&Value::str("state"))?.elements()?.iter() {
        match sequence_elements(pair)?.as_deref() {
            Some([Value::Int(index), state]) => states.push((*index, state.clone())),
            _ => fail_eval!("The states of a CounterExample should be pairs, but one is:\n{pair}"),
        }
    }
    states.sort_by_key(|(index, _)| *index);
    Ok(Value::tuple(states.into_iter().map(|(_, state)| state).collect()))
}

fn tlc_model_value(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    match arg(args, 0)? {
        Value::Str(name) => Ok(Value::Model(*name)),
        name => fail!("The argument of ModelValue should be a string, but instead it is:\n{name}"),
    }
}

fn tlc_fp(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let fingerprint = tlc_fingerprint(std::slice::from_ref(arg(args, 0)?))?;
    Ok(Value::Int(fingerprint as u32 as i32))
}

/// `TLCEvalDefinition("Name")`: the value of a zero-arity definition of the root module.
fn tlc_eval_definition(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let name = arg(args, 0)?;
    let def = match name {
        Value::Str(text) => match ctx.evaluator.spec.root.get(text) {
            Some(RootName::Def(def)) => Some(*def),
            _ => None,
        },
        _ => None,
    };
    let Some(def) = def else {
        fail!(
            "The argument of TLCEvalDefinition should be a name of a definition reachable from the root module, but instead it is:\n{name}"
        );
    };
    if !ctx.evaluator.spec.def(def).params.is_empty() {
        let Value::Str(text) = name else { unreachable!() };
        fail!(
            "The argument of TLCEvalDefinition should be a zero-arity definition, but instead it is:\n{text}"
        );
    }
    Ok(ctx.call(&Operator(OperatorKind::Def { def, parent: None }), &[])?)
}

/// The name `_Possible` counts under: a string's text, or another value as TLC prints it.
fn possible_name(value: &Value) -> Symbol {
    match value {
        Value::Str(name) => *name,
        _ => Symbol::intern(&value.to_string()),
    }
}

/// `_Track(expr, name)`: counts how often `expr` held under `name`.
fn track(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let name = possible_name(arg(args, 1)?);
    let holds = matches!(arg(args, 0)?, Value::Bool(true));
    let mut registers = ctx.runtime().registers.lock().unwrap();
    let count = registers.possible.entry(name).or_insert(0);
    *count = count.saturating_add(i32::from(holds));
    Ok(Value::TRUE)
}

fn counts(ctx: &mut Ctx<'_>, _: &[Arg]) -> Outcome {
    possible_counts(&ctx.runtime().registers.lock().unwrap().possible)
}

fn print_counts(ctx: &mut Ctx<'_>, _: &[Arg]) -> Outcome {
    let counts = counts(ctx, &[])?;
    ctx.runtime().print(strict_text(&counts)?);
    Ok(Value::TRUE)
}

fn check_name(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let name = possible_name(arg(args, 0)?);
    let count = ctx.runtime().registers.lock().unwrap().possible.get(&name).copied();
    if count.is_some_and(|count| count != 0) {
        return Ok(Value::TRUE);
    }
    print_counts(ctx, &[])?;
    Ok(Value::FALSE)
}

#[cfg(test)]
mod tests;
