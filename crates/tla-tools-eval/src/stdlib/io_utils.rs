//! The community module IOUtils, ported from CommunityModules' `tlc2/overrides/IOUtils.java` and
//! from the `Serialize` override of TLC's own `tlc2/module/Json.java`.
//!
//! TLC's Json class overrides IOUtils' `Serialize` for the NDJSON format whatever TLC's class path
//! holds, so [`lookup_builtin`] gives that native to every evaluator. The rest of IOUtils is Java
//! only when `CommunityModules-deps.jar` is on TLC's class path; otherwise TLC evaluates IOUtils'
//! TLA+ placeholders, as it did when the conformance corpus was recorded. [`lookup`] gives those
//! natives, which [`crate::Evaluator::with_community_modules`] installs.
//!
//! `zeroPadN` has no Java override: TLC evaluates its TLA+ definition. `IOSerialize` and
//! `IODeserialize` use Java's object serialization, which isn't ported: they fail, after
//! `IODeserialize` finds its file, as TLC does when it can't.

use tla_tools_value::{Error, Symbol, Value};

use super::tlc::pretty_print;
use super::{Failure, Outcome, arg, java_class, java_error, os_message};
use crate::{Arg, Ctx, Native};

/// A method of `tlc2.overrides.IOUtils` with the parameters TLC passes values of.
macro_rules! io_utils_method {
    ($result:literal, $name:literal, $parameters:literal) => {
        concat!("public static ", $result, " tlc2.overrides.IOUtils.", $name, "(", $parameters, ")")
    };
}

/// The [`Native`] of a definition TLC overrides with an `@Evaluation` method, which reports every
/// failure, its fallback to the TLA+ definition's included, as a failure of `signature`.
macro_rules! evaluation {
    ($operator:expr, $signature:expr) => {{
        fn native(
            ctx: &mut $crate::Ctx<'_>,
            args: &[$crate::Arg],
        ) -> tla_tools_value::Result<Value> {
            $operator(ctx, args).map_err(|failure: $crate::stdlib::Failure| {
                $crate::stdlib::java_error($signature, &failure.into_error().0)
            })
        }
        native as $crate::Native
    }};
}

mod process;
mod text;

const IO_SERIALIZE: &str = concat!(
    "public static final tlc2.value.IValue tlc2.overrides.IOUtils.ioSerialize(",
    "tlc2.value.IValue,tlc2.value.impl.StringValue,tlc2.value.impl.BoolValue",
    ") throws java.io.IOException"
);
const IO_DESERIALIZE: &str = concat!(
    "public static final tlc2.value.IValue tlc2.overrides.IOUtils.ioDeserialize(",
    "tlc2.value.impl.StringValue,tlc2.value.impl.BoolValue) throws java.io.IOException"
);

/// The natives TLC's own Java code gives IOUtils.
pub(super) fn lookup_builtin(name: &str) -> Option<Native> {
    match name {
        "Serialize" => Some(evaluation!(text::serialize::<false>, text::JSON_SERIALIZE)),
        _ => None,
    }
}

/// The natives of CommunityModules' IOUtils.
pub(super) fn lookup(name: &str) -> Option<Native> {
    Some(match name {
        "IOEnv" => {
            native!(|ctx: &mut Ctx<'_>, _: &[Arg]| -> Outcome { Ok(ctx.runtime().environment()) })
        }
        "atoi" => native!(atoi),
        "IOExec" => java!(process::io_exec, process::IO_EXEC),
        "IOEnvExec" => java!(process::io_env_exec, process::IO_ENV_EXEC),
        "IOExecTemplate" => java!(process::io_exec_template, process::IO_EXEC_TEMPLATE),
        "IOEnvExecTemplate" => {
            java!(process::io_env_exec_template, process::IO_ENV_EXEC_TEMPLATE)
        }
        "Serialize" => evaluation!(text::serialize::<true>, text::TEXT_SERIALIZE),
        "Deserialize" => evaluation!(text::deserialize, text::TEXT_DESERIALIZE),
        "IOSerialize" => native!(io_serialize),
        "IODeserialize" => native!(io_deserialize),
        _ => return None,
    })
}

/// TLC's `EC.TLC_MODULE_ONE_ARGUMENT_ERROR`, which IOUtils raises as an `EvalException`.
fn one_argument_error(name: &str, expected: &str, value: &Value) -> Failure {
    Failure::Module(Error(format!(
        "The argument of {name} should be a {expected}, but instead it is:\n{}",
        pretty_print(&value.to_string())
    )))
}

/// The record IOUtils' commands and text files return.
fn exec_record(exit_value: i32, stdout: &str, stderr: &str) -> Value {
    Value::record(vec![
        (Symbol::intern("exitValue"), Value::Int(exit_value)),
        (Symbol::intern("stdout"), Value::str(stdout)),
        (Symbol::intern("stderr"), Value::str(stderr)),
    ])
}

/// The message of Java's `ClassCastException` for a cast of `value` to `class`.
fn class_cast(value: &Value, class: &str) -> String {
    let from = format!("tlc2.value.impl.{}", java_class(value));
    format!(
        "class {from} cannot be cast to class tlc2.value.impl.{class} ({from} and tlc2.value.impl.{class} are in unnamed module of loader 'app')"
    )
}

/// The failure of a method handle that gets `value` for a parameter of type `class`.
fn parameter_cast(signature: &str, value: &Value, class: &str) -> Failure {
    let message =
        format!("Cannot cast tlc2.value.impl.{} to tlc2.value.impl.{class}", java_class(value));
    Failure::Eval(java_error(signature, &message))
}

/// `atoi(str)`, Java's `Integer.parseInt`.
fn atoi(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let value = arg(args, 0)?;
    match value {
        Value::Str(text) => match parse_int(text.as_str()) {
            Some(number) => Ok(Value::Int(number)),
            None => Err(one_argument_error("atoi", "string", value)),
        },
        _ => Err(one_argument_error("atoi", "string", value)),
    }
}

/// Java's `Integer.parseInt` for decimal digits: an optional sign, then at least one digit.
fn parse_int(text: &str) -> Option<i32> {
    let (negative, digits) = match text.as_bytes().first() {
        Some(b'-') => (true, &text[1..]),
        Some(b'+') => (false, &text[1..]),
        _ => (false, text),
    };
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let mut magnitude: i64 = 0;
    for digit in digits.bytes() {
        magnitude = magnitude * 10 + i64::from(digit - b'0');
        if magnitude > i64::from(i32::MAX) + 1 {
            return None;
        }
    }
    i32::try_from(if negative { -magnitude } else { magnitude }).ok()
}

/// `IOSerialize(val, absoluteFilename, compress)`, which writes Java's object serialization.
fn io_serialize(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let path = arg(args, 1)?;
    if !matches!(path, Value::Str(_)) {
        return Err(parameter_cast(IO_SERIALIZE, path, "StringValue"));
    }
    let compress = arg(args, 2)?;
    if !matches!(compress, Value::Bool(_)) {
        return Err(parameter_cast(IO_SERIALIZE, compress, "BoolValue"));
    }
    fail!("IOSerialize writes Java's object serialization format, which is not supported")
}

/// `IODeserialize(absoluteFilename, compressed)`, which reads Java's object serialization. It
/// first opens the file, as TLC does.
fn io_deserialize(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let path = match arg(args, 0)? {
        Value::Str(path) => path.as_str(),
        path => return Err(parameter_cast(IO_DESERIALIZE, path, "StringValue")),
    };
    let compressed = arg(args, 1)?;
    if !matches!(compressed, Value::Bool(_)) {
        return Err(parameter_cast(IO_DESERIALIZE, compressed, "BoolValue"));
    }
    // FileInputStream's FileNotFoundException.
    let reason = match std::fs::metadata(path) {
        Ok(metadata) if metadata.is_dir() => Some("Is a directory".to_owned()),
        Ok(_) => std::fs::File::open(path).err().map(|error| os_message(&error)),
        Err(error) => Some(os_message(&error)),
    };
    if let Some(reason) = reason {
        return Err(Failure::Eval(java_error(IO_DESERIALIZE, &format!("{path} ({reason})"))));
    }
    fail!("IODeserialize reads Java's object serialization format, which is not supported")
}

#[cfg(test)]
mod tests;
