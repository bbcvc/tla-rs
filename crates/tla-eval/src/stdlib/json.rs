//! Json, ported from tla-ts `json.ts`: TLC's conversions between values and JSON, and the files
//! `JsonSerialize` and the others read and write, by path relative to the working directory.

mod parser;

use std::fmt::Write;

use parser::Json;
use tla_value::{Symbol, Value};

use super::{
    Failure, Outcome, arg, argument_error, function_pairs, is_overridden_set, java_class,
    java_error, sequence_elements,
};
use crate::{Arg, Ctx, Native};

pub(super) fn lookup(name: &str) -> Option<Native> {
    Some(match name {
        "ToJson" => native!(to_json_native),
        "ToJsonArray" => native!(to_json_array),
        "ToJsonObject" => native!(to_json_object),
        "JsonSerialize" => native!(serialize),
        "ndJsonSerialize" => native!(nd_serialize),
        "JsonDeserialize" => native!(deserialize),
        "ndJsonDeserialize" => native!(nd_deserialize),
        _ => return None,
    })
}

/// A method of `tlc2.module.Json` as `java.lang.reflect.Method` prints it.
macro_rules! json_method {
    ($modifiers:literal, $result:literal, $name:literal, $parameters:literal) => {
        concat!(
            "public static ",
            $modifiers,
            $result,
            " tlc2.module.Json.",
            $name,
            "(",
            $parameters,
            ") throws java.io.IOException"
        )
    };
}

const TO_JSON: &str =
    json_method!("", "tlc2.value.impl.StringValue", "toJson", "tlc2.value.IValue");
const TO_JSON_ARRAY: &str =
    json_method!("", "tlc2.value.impl.StringValue", "toJsonArray", "tlc2.value.IValue");
const TO_JSON_OBJECT: &str =
    json_method!("", "tlc2.value.impl.StringValue", "toJsonObject", "tlc2.value.IValue");
const SERIALIZE: &str = json_method!(
    "synchronized ",
    "tlc2.value.impl.BoolValue",
    "serialize",
    "tlc2.value.impl.StringValue,tlc2.value.impl.Value"
);
const ND_SERIALIZE: &str = json_method!(
    "synchronized ",
    "tlc2.value.impl.BoolValue",
    "ndSerialize",
    "tlc2.value.impl.StringValue,tlc2.value.impl.Value"
);
const DESERIALIZE: &str =
    json_method!("", "tlc2.value.IValue", "deserialize", "tlc2.value.impl.StringValue");
const ND_DESERIALIZE: &str =
    json_method!("", "tlc2.value.IValue", "ndDeserialize", "tlc2.value.impl.StringValue");

fn java_failure(method: &str, message: &str) -> Failure {
    Failure::Eval(java_error(method, message))
}

fn unsupported(method: &str, value: &Value) -> Failure {
    let message = format!(
        "Cannot convert value: unsupported value type tlc2.value.impl.{}",
        java_class(value)
    );
    java_failure(method, &message)
}

/// A string as `JSON.stringify` writes it, with the line and paragraph separators escaped.
fn json_string(text: &str) -> String {
    let mut json = String::with_capacity(text.len() + 2);
    json.push('"');
    for char in text.chars() {
        match char {
            '"' => json.push_str("\\\""),
            '\\' => json.push_str("\\\\"),
            '\u{8}' => json.push_str("\\b"),
            '\u{c}' => json.push_str("\\f"),
            '\n' => json.push_str("\\n"),
            '\r' => json.push_str("\\r"),
            '\t' => json.push_str("\\t"),
            '\u{0}'..='\u{1f}' | '\u{2028}' | '\u{2029}' => {
                write!(json, "\\u{:04x}", char as u32).expect("writing to a string succeeds")
            }
            _ => json.push(char),
        }
    }
    json.push('"');
    json
}

fn to_json(value: &Value, method: &str) -> Outcome<String> {
    Ok(match value {
        Value::Str(text) => json_string(text.as_str()),
        Value::Bool(value) => value.to_string(),
        Value::Int(value) => value.to_string(),
        Value::Model(name) => json_string(name.as_str()),
        _ if value.is_set() => set_json(value, method)?,
        _ => function_json(value, method)?,
    })
}

fn set_json(set: &Value, method: &str) -> Outcome<String> {
    if is_overridden_set(set) {
        return Err(unsupported(method, set));
    }
    let elements = set.elements()?;
    let items = elements.iter().map(|element| to_json(element, method));
    Ok(format!("[{}]", items.collect::<Outcome<Vec<_>>>()?.join(",")))
}

fn function_json(function: &Value, method: &str) -> Outcome<String> {
    let function = function.materialize()?;
    if let Value::Tuple(items) = &function {
        let items = items.iter().map(|item| to_json(item, method));
        return Ok(format!("[{}]", items.collect::<Outcome<Vec<_>>>()?.join(",")));
    }
    let mut fields = Vec::new();
    for (key, value) in function_pairs(&function)? {
        let key = match key {
            Value::Str(text) => json_string(text.as_str()),
            key => json_string(&key.to_string()),
        };
        fields.push(format!("{key}:{}", to_json(&value, method)?));
    }
    Ok(format!("{{{}}}", fields.join(",")))
}

/// Whether TLC takes a value for a record: a function whose nonempty domain is all strings.
fn is_record(value: &Value) -> Outcome<bool> {
    if !value.is_function() {
        return Ok(false);
    }
    let pairs = function_pairs(&value.materialize()?)?;
    Ok(!pairs.is_empty() && pairs.iter().all(|(key, _)| matches!(key, Value::Str(_))))
}

fn to_json_native(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    Ok(Value::str(&to_json(arg(args, 0)?, TO_JSON)?))
}

fn to_json_array(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let value = arg(args, 0)?;
    if value.is_set() {
        return Ok(Value::str(&set_json(value, TO_JSON_ARRAY)?));
    }
    if !value.is_function() || is_record(value)? {
        return Err(unsupported(TO_JSON_ARRAY, value));
    }
    Ok(Value::str(&function_json(value, TO_JSON_ARRAY)?))
}

fn to_json_object(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let value = arg(args, 0)?;
    if !value.is_function() {
        return Err(unsupported(TO_JSON_OBJECT, value));
    }
    Ok(Value::str(&function_json(value, TO_JSON_OBJECT)?))
}

fn path<'a>(value: &'a Value, method: &str) -> Outcome<&'a str> {
    match value {
        Value::Str(path) => Ok(path.as_str()),
        _ => Err(java_failure(
            method,
            &format!(
                "Cannot cast tlc2.value.impl.{} to tlc2.value.impl.StringValue",
                java_class(value)
            ),
        )),
    }
}

fn write_file(path: &str, content: &str, method: &str) -> Outcome<()> {
    std::fs::write(path, content)
        .map_err(|error| java_failure(method, &format!("{path} ({error})")))
}

fn read_file(path: &str, method: &str) -> Outcome<String> {
    std::fs::read_to_string(path)
        .map_err(|_| java_failure(method, &format!("{path} (No such file or directory)")))
}

fn serialize(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let path = path(arg(args, 0)?, SERIALIZE)?;
    let value = arg(args, 1)?;
    if sequence_elements(value)?.is_none() && !is_record(value)? {
        return Err(argument_error("second", "JsonSerialize", "sequence or record", value));
    }
    write_file(path, &to_json(value, SERIALIZE)?, SERIALIZE)?;
    Ok(Value::TRUE)
}

fn nd_serialize(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let path = path(arg(args, 0)?, ND_SERIALIZE)?;
    let value = arg(args, 1)?;
    let Some(elements) = sequence_elements(value)? else {
        return Err(argument_error("second", "ndJsonSerialize", "sequence", value));
    };
    let mut content = String::new();
    for element in elements.iter() {
        content.push_str(&to_json(element, ND_SERIALIZE)?);
        content.push('\n');
    }
    write_file(path, &content, ND_SERIALIZE)?;
    Ok(Value::TRUE)
}

fn deserialize(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let path = path(arg(args, 0)?, DESERIALIZE)?;
    parse_json(&read_file(path, DESERIALIZE)?, DESERIALIZE)
}

fn nd_deserialize(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let path = path(arg(args, 0)?, ND_DESERIALIZE)?;
    let text = read_file(path, ND_DESERIALIZE)?;
    let lines = text.split(['\n', '\r']).map(str::trim).filter(|line| !line.is_empty());
    let values = lines.map(|line| parse_json(line, ND_DESERIALIZE));
    Ok(Value::tuple(values.collect::<Outcome<_>>()?))
}

/// Reads JSON as TLC does: an empty text is null, which no value stands for.
fn parse_json(text: &str, method: &str) -> Outcome {
    let json = if text.trim().is_empty() {
        Json::Null
    } else {
        parser::parse(text).map_err(|message| java_failure(method, &message))?
    };
    from_json(json, method)
}

fn from_json(json: Json, method: &str) -> Outcome {
    Ok(match json {
        Json::Null => {
            return Err(java_failure(method, "Cannot convert value: unsupported JSON value null"));
        }
        Json::Bool(value) => Value::Bool(value),
        Json::Number(source) => Value::Int(json_integer(&source)),
        Json::String(text) => Value::str(&text),
        Json::Array(items) => Value::tuple(
            items.into_iter().map(|item| from_json(item, method)).collect::<Outcome<_>>()?,
        ),
        Json::Object(members) => {
            let mut fields = Vec::with_capacity(members.len());
            for (key, member) in js_member_order(members) {
                let name = Symbol::intern(&key);
                fields.push((name, from_json(member, method)?));
            }
            Value::record(fields)
        }
    })
}

/// The members of an object in the order `Object.entries` gives them: integer keys first in
/// ascending order, then the others as written, each key once with its last value.
fn js_member_order(members: Vec<(String, Json)>) -> Vec<(String, Json)> {
    let mut unique: Vec<(String, Json)> = Vec::with_capacity(members.len());
    for (key, member) in members {
        match unique.iter_mut().find(|(known, _)| *known == key) {
            Some(entry) => entry.1 = member,
            None => unique.push((key, member)),
        }
    }
    let index = |key: &str| -> Option<u32> {
        let is_canonical = key == "0" || (!key.starts_with('0') && !key.is_empty());
        key.parse::<u32>().ok().filter(|&index| is_canonical && index != u32::MAX)
    };
    let (mut indices, names): (Vec<_>, Vec<_>) =
        unique.into_iter().partition(|(key, _)| index(key).is_some());
    indices.sort_by_key(|(key, _)| index(key));
    indices.into_iter().chain(names).collect()
}

/// A JSON number as Gson's `intValue` reads it: the exact decimal truncated toward zero, keeping
/// its low 32 bits.
fn json_integer(source: &str) -> i32 {
    let (negative, rest) = match source.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, source),
    };
    let (mantissa, exponent) = match rest.find(['e', 'E']) {
        Some(index) => (&rest[..index], rest[index + 1..].parse::<i64>().unwrap_or(i64::MAX)),
        None => (rest, 0),
    };
    let (whole, fraction) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let digits = format!("{whole}{fraction}");
    let shift = exponent.saturating_sub(fraction.len() as i64);
    // Dropping digits truncates; each further factor of 10 is a factor of 2, and 32 of them
    // leave nothing of the low 32 bits.
    let kept = if shift < 0 {
        &digits[..digits.len().saturating_sub(shift.unsigned_abs() as usize)]
    } else {
        &digits
    };
    let mut value = kept
        .bytes()
        .fold(0u32, |value, digit| value.wrapping_mul(10).wrapping_add(u32::from(digit - b'0')));
    for _ in 0..shift.clamp(0, 32) {
        value = value.wrapping_mul(10);
    }
    if negative { value.wrapping_neg() as i32 } else { value as i32 }
}

#[cfg(test)]
mod tests;
