//! `TLCGet` and `TLCSet`, ported from tla-ts `tlc/tlc-operators.ts` and `setTlcValue` of
//! `tlc/tlcext-operators.ts`: numbered and named registers, Java system properties, and what
//! TLC reports about itself and its model checker.

use std::sync::atomic::Ordering;
use std::time::{SystemTime, UNIX_EPOCH};

use tla_value::{Symbol, Value};

use crate::stdlib::{Outcome, arg};
use crate::{Arg, Ctx, Runtime};

/// The prefix of the keys of named registers.
const NAMED_REGISTER_PREFIX: &str = "s:";

/// The named register `_Possible` keeps its counts in.
const POSSIBLE_REGISTER: &str = "s:_possible";

/// The keys TLCGet can't read before TLC creates its model checker.
const CHECKER_KEYS: [&str; 6] = ["diameter", "generated", "distinct", "queue", "stats", "config"];

pub(super) fn tlc_get(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let key = arg(args, 0)?;
    let runtime = ctx.runtime();
    match key {
        Value::Int(index) if *index >= 0 => {
            match runtime.registers.lock().unwrap().numbered.get(index) {
                Some(value) => Ok(value.clone()),
                None => fail!("TLCGet({key}) was undefined."),
            }
        }
        Value::Str(name) => runtime_value(ctx, name.as_str()),
        _ => fail!(
            "The argument of TLCGet should be a nonnegative integer, but instead it is:\n{key}"
        ),
    }
}

fn int(value: i64) -> Value {
    Value::Int(i32::try_from(value).unwrap_or(i32::MAX))
}

fn record(fields: Vec<(&str, Value)>) -> Value {
    Value::record(fields.into_iter().map(|(name, value)| (Symbol::intern(name), value)).collect())
}

/// What `TLCGet(key)` reads for a string key.
fn runtime_value(ctx: &Ctx<'_>, key: &str) -> Outcome {
    let runtime = ctx.runtime();
    let statistics = runtime.statistics();
    if statistics.is_none() && CHECKER_KEYS.contains(&key) {
        fail!("TLCGet({key}) was undefined.");
    }
    let statistics = statistics.unwrap_or_default();
    let duration = int(runtime.elapsed().as_secs() as i64);
    Ok(match key {
        "level" => Value::Int(runtime.level(ctx.state())),
        "diameter" => int(statistics.diameter),
        "generated" => int(statistics.generated),
        "distinct" => int(statistics.distinct),
        "queue" => int(statistics.queue),
        "duration" => duration,
        "stats" => record(vec![
            ("queue", int(statistics.queue)),
            ("distinct", int(statistics.distinct)),
            ("initial", int(statistics.initial)),
            ("generated", int(statistics.generated)),
            ("diameter", int(statistics.diameter)),
            ("duration", duration),
            ("worker", Value::Int(0)),
        ]),
        "config" => record(vec![
            ("mode", Value::str("bfs")),
            ("deadlock", Value::Bool(runtime.checks_deadlock())),
            ("worker", Value::Int(1)),
            ("seed", Value::str(&runtime.seed().to_string())),
            ("fingerprint", Value::str("0")),
            ("install", Value::str("unknown")),
        ]),
        "revision" => revision(runtime),
        "spec" => runtime.spec().unwrap_or_else(|| record(Vec::new())),
        "action" => action_record(),
        "all" => {
            let registers = runtime.registers.lock().unwrap();
            let pairs = registers.numbered.iter().map(|(index, value)| (Value::Int(*index), value));
            register_function(pairs)?
        }
        "all:named" => register_function(
            named_registers(runtime)?.iter().map(|(key, value)| (Value::Str(*key), value)),
        )?,
        _ if key.starts_with(NAMED_REGISTER_PREFIX) => {
            match named_registers(runtime)?.into_iter().find(|(name, _)| name.as_str() == key) {
                Some((_, value)) => value,
                None => fail!("TLCGet({key}) was undefined."),
            }
        }
        _ if key.starts_with("-D") => {
            let registers = runtime.registers.lock().unwrap();
            Value::str(registers.properties.get(&key[2..]).map_or(key, String::as_str))
        }
        _ => fail!("TLCGet({key}) was undefined."),
    })
}

/// The registers as a function from each key to a tuple of its value in each worker.
fn register_function<'a>(pairs: impl Iterator<Item = (Value, &'a Value)>) -> Outcome {
    let pairs = pairs.map(|(key, value)| (key, Value::tuple(vec![value.clone()])));
    Ok(Value::function(pairs.collect())?)
}

/// The named registers, with the counts of `_Possible` once it has counted something.
fn named_registers(runtime: &Runtime) -> Outcome<Vec<(Symbol, Value)>> {
    let registers = runtime.registers.lock().unwrap();
    let mut named: Vec<(Symbol, Value)> =
        registers.named.iter().map(|(key, value)| (*key, value.clone())).collect();
    if !registers.possible.is_empty() {
        let counts = possible_counts(&registers.possible)?;
        let key = Symbol::intern(POSSIBLE_REGISTER);
        named.retain(|(name, _)| *name != key);
        named.push((key, counts));
    }
    Ok(named)
}

/// The counts of `_Possible` as a function from each name to its count.
fn possible_counts(counts: &std::collections::BTreeMap<Symbol, i32>) -> Outcome {
    let pairs = counts.iter().map(|(name, count)| (Value::Str(*name), Value::Int(*count)));
    Ok(Value::function(pairs.collect())?)
}

/// TLC's record for an action it doesn't store, as every action in breadth-first search.
fn action_record() -> Value {
    let location = record(vec![
        ("beginLine", Value::Int(0)),
        ("beginColumn", Value::Int(0)),
        ("endLine", Value::Int(0)),
        ("endColumn", Value::Int(0)),
        ("module", Value::str("--TLA+ BUILTINS--")),
    ]);
    record(vec![("name", Value::str("UnnamedAction")), ("location", location)])
}

/// The civil date and time of `time` in UTC: year, month, day, hour, minute, second, and
/// millisecond.
fn utc(time: SystemTime) -> [i64; 7] {
    let since_epoch = time.duration_since(UNIX_EPOCH).unwrap_or_default();
    let seconds = since_epoch.as_secs() as i64;
    let (days, of_day) = (seconds.div_euclid(86_400), seconds.rem_euclid(86_400));
    // Howard Hinnant's days_from_civil, inverted.
    let shifted = days + 719_468;
    let era = shifted.div_euclid(146_097);
    let day_of_era = shifted.rem_euclid(146_097);
    let year_of_era =
        (day_of_era - day_of_era / 1460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let month_index = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * month_index + 2) / 5 + 1;
    let month = if month_index < 10 { month_index + 3 } else { month_index - 9 };
    let year = year_of_era + era * 400 + i64::from(month <= 2);
    let millisecond = i64::from(since_epoch.subsec_millis());
    [year, month, day, of_day / 3600, of_day / 60 % 60, of_day % 60, millisecond]
}

/// `TLCGet("revision")`, for a development build of TLC.
fn revision(runtime: &Runtime) -> Value {
    let now = SystemTime::now();
    let [year, month, day, hour, minute, second, millisecond] = utc(now);
    let date =
        format!("{year:04}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}.{millisecond}Z");
    let [year, month, day, hour, minute, second, _] = utc(runtime.started_at());
    let calver = format!("{year}.{month:02}.{day:02}.{hour:02}{minute:02}{second:02}");
    let timestamp = now.duration_since(UNIX_EPOCH).unwrap_or_default().as_secs() as i64;
    record(vec![
        ("count", Value::Int(0)),
        ("timestamp", int(timestamp)),
        ("date", Value::str(&date)),
        ("tag", Value::str("development")),
        ("calver", Value::str(&calver)),
    ])
}

pub(super) fn tlc_set(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    set_register(ctx.runtime(), arg(args, 0)?, arg(args, 1)?.clone())?;
    Ok(Value::TRUE)
}

/// `TLCSet(key, value)`.
fn set_register(runtime: &Runtime, key: &Value, value: Value) -> Outcome<()> {
    match key {
        Value::Int(index) if *index >= 0 => {
            runtime.registers.lock().unwrap().numbered.insert(*index, value);
        }
        Value::Str(name) if name.as_str() == "exit" => {
            if matches!(value, Value::Bool(true)) {
                runtime.is_stopped.store(true, Ordering::SeqCst);
            }
        }
        Value::Str(name) if name.as_str() == "pause" => {
            if matches!(value, Value::Bool(true)) {
                runtime.print("Press enter to resume model checking.".to_owned());
            }
        }
        Value::Str(name) if name.as_str().starts_with(NAMED_REGISTER_PREFIX) => {
            runtime.registers.lock().unwrap().named.insert(*name, value);
        }
        Value::Str(name) if name.as_str().starts_with("-D") => {
            let property = name.as_str()[2..].to_owned();
            runtime.registers.lock().unwrap().properties.insert(property, value.to_string());
        }
        _ => fail!(
            "The first argument of TLCSet should be a nonnegative integer, but instead it is:\n{key}"
        ),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::time::{Duration, UNIX_EPOCH};

    use tla_value::{Result, Value};

    use super::utc;
    use crate::Arg;
    use crate::stdlib::testing::{call_in, evaluator, int, string};

    fn tlc(evaluator: &crate::Evaluator, name: &str, args: &[Value]) -> Result<Value> {
        let args = args.iter().cloned().map(Arg::Value).collect();
        call_in(evaluator, "TLC", name, false, args)
    }

    const TLC_GET_EVAL: &str = "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLCGetSet.TLCGetEval(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel),\nbut it produced the following error:\n";

    #[test]
    fn keeps_registers() {
        let evaluator = evaluator();
        assert_eq!(
            tlc(&evaluator, "TLCSet", &[int(3), string("x")]).unwrap().as_bool(),
            Some(true)
        );
        assert_eq!(tlc(&evaluator, "TLCGet", &[int(3)]).unwrap().to_string(), "\"x\"");
        assert_eq!(
            tlc(&evaluator, "TLCGet", &[int(4)]).unwrap_err().0,
            format!("{TLC_GET_EVAL}TLCGet(4) was undefined.")
        );
        tlc(&evaluator, "TLCSet", &[string("s:a"), int(1)]).unwrap();
        assert_eq!(tlc(&evaluator, "TLCGet", &[string("s:a")]).unwrap().as_int(), Some(1));
        assert_eq!(
            tlc(&evaluator, "TLCGet", &[string("all")]).unwrap().to_string(),
            "(3 :> <<\"x\">>)"
        );
        assert_eq!(
            tlc(&evaluator, "TLCGet", &[string("all:named")]).unwrap().to_string(),
            "(\"s:a\" :> <<1>>)"
        );
        tlc(&evaluator, "TLCSet", &[string("-Dkey"), string("v")]).unwrap();
        assert_eq!(
            tlc(&evaluator, "TLCGet", &[string("-Dkey")]).unwrap().to_string(),
            "\"\\\"v\\\"\""
        );
        assert_eq!(
            tlc(&evaluator, "TLCGet", &[string("-Dother")]).unwrap().to_string(),
            "\"-Dother\""
        );
        tlc(&evaluator, "TLCSet", &[string("exit"), Value::TRUE]).unwrap();
        assert!(evaluator.runtime().is_stopped.load(std::sync::atomic::Ordering::SeqCst));
        assert_eq!(
            tlc(&evaluator, "TLCSet", &[int(-1), int(0)]).unwrap_err().0,
            "The first argument of TLCSet should be a nonnegative integer, but instead it is:\n-1"
        );
        assert_eq!(
            tlc(&evaluator, "TLCGet", &[int(-1)]).unwrap_err().0,
            format!(
                "{TLC_GET_EVAL}The argument of TLCGet should be a nonnegative integer, but instead it is:\n-1"
            )
        );
    }

    #[test]
    fn reports_the_model_checker() {
        let evaluator = evaluator();
        assert_eq!(tlc(&evaluator, "TLCGet", &[string("level")]).unwrap().as_int(), Some(0));
        assert_eq!(
            tlc(&evaluator, "TLCGet", &[string("distinct")]).unwrap_err().0,
            format!("{TLC_GET_EVAL}TLCGet(distinct) was undefined.")
        );
        evaluator.runtime().set_seed(-42);
        evaluator.runtime().start(false);
        evaluator.runtime().update_statistics(|statistics| statistics.distinct = 9);
        assert_eq!(tlc(&evaluator, "TLCGet", &[string("distinct")]).unwrap().as_int(), Some(9));
        let config = tlc(&evaluator, "TLCGet", &[string("config")]).unwrap();
        let field = |name: &str| config.field(tla_value::Symbol::intern(name)).unwrap().to_string();
        assert_eq!(
            (field("seed"), field("deadlock"), field("mode")),
            ("\"-42\"".into(), "FALSE".into(), "\"bfs\"".into())
        );
        let action = tlc(&evaluator, "TLCGet", &[string("action")]).unwrap();
        assert_eq!(
            action.field(tla_value::Symbol::intern("name")).unwrap().to_string(),
            "\"UnnamedAction\""
        );
        assert!(tlc(&evaluator, "TLCGet", &[string("revision")]).is_ok());
        assert!(tlc(&evaluator, "TLCGet", &[string("nothing")]).is_err());
    }

    #[test]
    fn converts_times_to_utc_dates() {
        assert_eq!(utc(UNIX_EPOCH), [1970, 1, 1, 0, 0, 0, 0]);
        let time = UNIX_EPOCH + Duration::from_millis(1_709_251_199_123);
        assert_eq!(utc(time), [2024, 2, 29, 23, 59, 59, 123]);
    }
}
