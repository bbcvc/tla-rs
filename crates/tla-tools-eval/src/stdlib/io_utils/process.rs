//! IOUtils' `IOExec`, `IOEnvExec`, `IOExecTemplate`, and `IOEnvExecTemplate`, which run a command
//! and return its exit value and output. They run nothing unless the runtime allows it
//! ([`crate::Runtime::allow_exec`]).

use std::process::{Command, Stdio};

use tla_tools_value::{Error, Value};

use super::{exec_record, one_argument_error};
use crate::stdlib::{Failure, Outcome, arg, os_message};
use crate::{Arg, Ctx};

/// The exceptions an IOUtils command method declares.
macro_rules! exec_method {
    ($name:literal, $parameters:literal) => {
        concat!(
            io_utils_method!("tlc2.value.impl.Value", $name, $parameters),
            " throws java.io.IOException,java.lang.InterruptedException"
        )
    };
}

pub(super) const IO_EXEC: &str = exec_method!("ioExec", "tlc2.value.impl.Value");
pub(super) const IO_ENV_EXEC: &str =
    exec_method!("ioEnvExec", "tlc2.value.impl.Value,tlc2.value.impl.Value");
pub(super) const IO_EXEC_TEMPLATE: &str =
    exec_method!("ioExecTemplate", "tlc2.value.impl.Value,tlc2.value.impl.Value");
pub(super) const IO_ENV_EXEC_TEMPLATE: &str = exec_method!(
    "ioEnvExecTemplate",
    "tlc2.value.impl.Value,tlc2.value.impl.Value,tlc2.value.impl.Value"
);

/// The strings of a sequence argument, as `TupleValue`s of `StringValue`s. IOUtils names
/// `IOExec` in the error for any element that isn't a string.
fn strings(value: &Value, name: &str) -> Outcome<Vec<String>> {
    let Value::Tuple(items) = value else {
        return Err(one_argument_error(name, "sequence", value));
    };
    let strings = items.iter().map(|item| match item {
        Value::Str(text) => Ok(text.as_str().to_owned()),
        _ => Err(one_argument_error("IOExec", "sequence", item)),
    });
    strings.collect()
}

/// The environment variables of a record, each value as TLC prints it without quotes.
fn environment(value: &Value, name: &str) -> Outcome<Vec<(String, String)>> {
    let record = value.materialize()?;
    let fields = match &record {
        Value::Func(func) if func.keys.iter().all(|key| matches!(key, Value::Str(_))) => {
            func.keys.iter().zip(func.values.iter()).collect::<Vec<_>>()
        }
        Value::Tuple(items) if items.is_empty() => Vec::new(),
        _ => return Err(one_argument_error(name, "record", value)),
    };
    let unquoted = |value: &Value| match value {
        Value::Str(text) => text.as_str().to_owned(),
        _ => value.to_string(),
    };
    let fields = fields.into_iter().map(|(key, value)| (unquoted(key), unquoted(value)));
    Ok(fields.collect())
}

pub(super) fn io_exec(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let command = strings(arg(args, 0)?, "IOExec")?;
    run(ctx, "IOExec", &command, &[])
}

pub(super) fn io_env_exec(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let environment = environment(arg(args, 0)?, "IOEnvExec")?;
    let command = strings(arg(args, 1)?, "IOEnvExec")?;
    run(ctx, "IOEnvExec", &command, &environment)
}

pub(super) fn io_exec_template(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let command = templated(arg(args, 0)?, arg(args, 1)?, "IOExecTemplate")?;
    run(ctx, "IOExecTemplate", &command, &[])
}

pub(super) fn io_env_exec_template(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let environment = environment(arg(args, 0)?, "IOEnvExecTemplate")?;
    let command = templated(arg(args, 1)?, arg(args, 2)?, "IOEnvExecTemplate")?;
    run(ctx, "IOEnvExecTemplate", &command, &environment)
}

/// Each element of the template formatted with all the parameters, as `String.format` does.
fn templated(template: &Value, parameters: &Value, name: &str) -> Outcome<Vec<String>> {
    if !matches!(template, Value::Tuple(_)) {
        return Err(one_argument_error(name, "sequence", template));
    }
    if !matches!(parameters, Value::Tuple(_)) {
        return Err(one_argument_error(name, "sequence", parameters));
    }
    let (template, parameters) = (strings(template, name)?, strings(parameters, name)?);
    let command = template.iter().map(|part| java_format(part, &parameters));
    command.collect::<Result<_, _>>().map_err(|message| Failure::Eval(Error(message)))
}

/// Runs `command` with `environment` added to this process's, as Java's `ProcessBuilder` does,
/// and returns its exit value and output.
fn run(
    ctx: &mut Ctx<'_>,
    name: &str,
    command: &[String],
    environment: &[(String, String)],
) -> Outcome {
    if !ctx.runtime().allows_exec() {
        let command = Value::tuple(command.iter().map(|part| Value::str(part)).collect());
        fail!(
            "{name} would run the command {command}, but running commands is off: Runtime::allow_exec turns it on"
        );
    }
    let Some((program, arguments)) = command.split_first() else {
        fail_eval!("Index 0 out of bounds for length 0");
    };
    let output = Command::new(program)
        .args(arguments)
        .envs(environment.iter().cloned())
        .stdin(Stdio::null())
        .output();
    let output = match output {
        Ok(output) => output,
        Err(error) => fail_eval!(
            "Cannot run program \"{program}\": error={}, {}",
            error.raw_os_error().unwrap_or(0),
            os_message(&error)
        ),
    };
    let exit_value = output.status.code().unwrap_or_else(|| {
        // Java reports a process a signal ended with 128 plus the signal's number.
        #[cfg(unix)]
        {
            use std::os::unix::process::ExitStatusExt;
            128 + output.status.signal().unwrap_or(0)
        }
        #[cfg(not(unix))]
        {
            1
        }
    });
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    Ok(exec_record(exit_value, &stdout, &stderr))
}

/// `String.format(template, arguments)` for string arguments, or the message of the exception
/// Java's `Formatter` raises. It reads `%[index$][flags][width][.precision]conversion`.
pub(super) fn java_format(template: &str, arguments: &[String]) -> Result<String, String> {
    let chars: Vec<char> = template.chars().collect();
    let mut text = String::new();
    let (mut position, mut ordinary, mut last) = (0, 0usize, None::<usize>);
    while position < chars.len() {
        if chars[position] != '%' {
            text.push(chars[position]);
            position += 1;
            continue;
        }
        let start = position;
        position += 1;
        let digits = |position: &mut usize| {
            let from = *position;
            while *position < chars.len() && chars[*position].is_ascii_digit() {
                *position += 1;
            }
            chars[from..*position].iter().collect::<String>()
        };
        let mut index = None;
        let number = digits(&mut position);
        let mut width = None;
        if !number.is_empty() && chars.get(position) == Some(&'$') {
            index = number.parse::<usize>().ok();
            position += 1;
        } else if !number.is_empty() {
            width = number.parse::<usize>().ok();
        }
        let mut flags = String::new();
        if width.is_none() {
            while let Some(&flag @ ('-' | '#' | '+' | ' ' | '0' | ',' | '(' | '<')) =
                chars.get(position)
            {
                flags.push(flag);
                position += 1;
            }
            let number = digits(&mut position);
            width = number.parse::<usize>().ok();
        }
        let mut precision = None;
        if chars.get(position) == Some(&'.') {
            position += 1;
            precision = digits(&mut position).parse::<usize>().ok();
        }
        let Some(&conversion) = chars.get(position) else {
            return Err("Conversion = '%'".to_owned());
        };
        position += 1;
        let specifier: String = chars[start..position].iter().collect();
        let value = match conversion {
            '%' => "%".to_owned(),
            'n' => "\n".to_owned(),
            's' | 'S' | 'b' | 'B' | 'h' | 'H' => {
                if let Some(flag) = flags.chars().find(|flag| !matches!(flag, '-' | '<')) {
                    return Err(format!("Conversion = {conversion}, Flags = {flag}"));
                }
                if flags.contains('-') && width.is_none() {
                    return Err(specifier);
                }
                let argument = if flags.contains('<') {
                    last
                } else if let Some(index) = index {
                    index.checked_sub(1)
                } else {
                    ordinary += 1;
                    Some(ordinary - 1)
                };
                let Some(argument) = argument.filter(|&argument| argument < arguments.len()) else {
                    return Err(format!("Format specifier '{specifier}'"));
                };
                last = Some(argument);
                let argument = &arguments[argument];
                let value = match conversion.to_ascii_lowercase() {
                    's' => argument.clone(),
                    'b' => "true".to_owned(),
                    _ => format!("{:x}", java_hash_code(argument)),
                };
                if conversion.is_ascii_uppercase() { value.to_uppercase() } else { value }
            }
            'c' | 'd' | 'o' | 'x' | 'X' | 'e' | 'E' | 'f' | 'g' | 'G' | 'a' | 'A' | 't' | 'T' => {
                return Err(format!("{conversion} != java.lang.String"));
            }
            _ => return Err(format!("Conversion = '{conversion}'")),
        };
        let value: String = match precision {
            Some(precision) => value.chars().take(precision).collect(),
            None => value,
        };
        let padding = width.unwrap_or(0).saturating_sub(value.chars().count());
        if flags.contains('-') {
            text.push_str(&value);
            text.extend(std::iter::repeat_n(' ', padding));
        } else {
            text.extend(std::iter::repeat_n(' ', padding));
            text.push_str(&value);
        }
    }
    Ok(text)
}

/// Java's `String#hashCode`.
fn java_hash_code(text: &str) -> u32 {
    text.encode_utf16().fold(0u32, |hash, unit| hash.wrapping_mul(31).wrapping_add(u32::from(unit)))
}
