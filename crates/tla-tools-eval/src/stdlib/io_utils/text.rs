//! IOUtils' `Serialize` and `Deserialize`, which TLC overrides with a chain of `@Evaluation`
//! methods by priority: its Json class writes NDJSON, CommunityModules' IOUtils reads and writes
//! plain text (TXT), and a format neither handles falls back to the TLA+ definition.
//!
//! Each method evaluates its own arguments. The plain text methods report a failure to evaluate
//! their arguments or to use the file in the record they return; everything else fails.

use std::io::Write;

use tla_tools_value::{Error, Value};

use super::{class_cast, exec_record};
use crate::stdlib::json::{unsupported_message, value_json};
use crate::stdlib::{Failure, Outcome, argument_error, forced, os_message, sequence_elements};
use crate::{Arg, Ctx};

/// An `@Evaluation` method, which TLC hands the expressions of the arguments.
macro_rules! evaluation_method {
    ($class:literal, $name:literal) => {
        concat!(
            "public static synchronized tlc2.value.impl.Value ",
            $class,
            ".",
            $name,
            "(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,",
            "tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel)"
        )
    };
}

pub(super) const JSON_SERIALIZE: &str = evaluation_method!("tlc2.module.Json", "textSerialize");
pub(super) const TEXT_SERIALIZE: &str =
    evaluation_method!("tlc2.overrides.IOUtils", "textSerialize");
pub(super) const TEXT_DESERIALIZE: &str =
    evaluation_method!("tlc2.overrides.IOUtils", "textDeserialize");

/// `Serialize(value, dest, options)`: TLC's Json class, then CommunityModules' IOUtils if
/// `COMMUNITY`, then the TLA+ definition.
pub(super) fn serialize<const COMMUNITY: bool>(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    if let Some(value) = ndjson_serialize(ctx, args)? {
        return Ok(value);
    }
    if COMMUNITY && let Some(value) = text_serialize(ctx, args)? {
        return Ok(value);
    }
    Ok(ctx.evaluate_definition()?)
}

/// `Deserialize(src, options)`: CommunityModules' IOUtils, then the TLA+ definition.
pub(super) fn deserialize(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    if let Some(value) = text_deserialize(ctx, args)? {
        return Ok(value);
    }
    Ok(ctx.evaluate_definition()?)
}

/// A value as a record, as TLC's `toRcd` converts it: a function from strings.
fn to_record(value: &Value) -> Option<&Value> {
    match value {
        Value::Func(func) if func.keys.iter().all(|key| matches!(key, Value::Str(_))) => {
            Some(value)
        }
        Value::Tuple(items) if items.is_empty() => Some(value),
        _ => None,
    }
}

/// The string field `name` of the options, as `(StringValue) opts.apply(name)` reads it.
fn string_option(options: &Value, name: &str) -> Outcome<String> {
    match options.apply(&Value::str(name))? {
        Value::Str(text) => Ok(text.as_str().to_owned()),
        value => Err(Failure::Eval(Error(class_cast(&value, "StringValue")))),
    }
}

/// The open options of the options, as `(TupleValue) opts.apply("openOptions")` reads them, each
/// cast to a string.
fn open_option_names(options: &Value) -> Outcome<Vec<String>> {
    let names = match options.apply(&Value::str("openOptions"))? {
        Value::Tuple(items) => items,
        value => return Err(Failure::Eval(Error(class_cast(&value, "TupleValue")))),
    };
    let names = names.iter().map(|name| match name {
        Value::Str(name) => Ok(name.as_str().to_owned()),
        name => Err(Failure::Eval(Error(class_cast(name, "StringValue")))),
    });
    names.collect()
}

/// `tlc2.module.Json#textSerialize`, which writes a sequence of values as newline delimited JSON.
fn ndjson_serialize(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome<Option<Value>> {
    let third = forced(ctx, args, 2)?;
    let Some(options) = to_record(&third) else {
        return Err(argument_error("third", "ndJsonSerialize", "sequence", &third));
    };
    if string_option(options, "format")? != "NDJSON" {
        return Ok(None);
    }
    let first = forced(ctx, args, 0)?;
    let Some(payload) = sequence_elements(&first)? else {
        return Err(argument_error("first", "Serialize", "sequence", &first));
    };
    let second = forced(ctx, args, 1)?;
    let Value::Str(path) = second else {
        return Err(argument_error("second", "ndJsonSerialize", "sequence", &second));
    };
    let open_options = open_option_names(options)?;
    let charset = string_option(options, "charset")?;
    let lines = |charset: Charset, file: &mut std::fs::File| -> Result<(), String> {
        for element in payload.iter() {
            let unsupported = |value: &Value| {
                Failure::Eval(Error(format!("java.io.IOException: {}", unsupported_message(value))))
            };
            let line =
                value_json(element, &unsupported).map_err(|failure| failure.into_error().0)?;
            let bytes = charset.encode(&format!("{line}\n"))?;
            file.write_all(&bytes).map_err(|error| java_io_exception(&error, path.as_str()))?;
        }
        Ok(())
    };
    // TLC wraps the failure of the write in a RuntimeException, whose message is the exception's
    // text.
    let written = Charset::named(&charset).and_then(|charset| {
        let mut file = open(path.as_str(), &open_options)?;
        lines(charset, &mut file)
    });
    match written {
        Ok(()) => Ok(Some(Value::TRUE)),
        Err(exception) => Err(Failure::Eval(Error(exception))),
    }
}

/// The parameters of a plain text method, or the text of the exception that evaluating them
/// raised.
type Parameters<T> = std::result::Result<T, String>;

/// What a plain text method reports of a failure to evaluate a parameter: its message, where TLC
/// reports the Java exception's class and message.
fn exception_text(failure: Failure) -> String {
    failure.into_error().0
}

fn string_parameter(ctx: &mut Ctx<'_>, args: &[Arg], index: usize) -> Parameters<String> {
    match forced(ctx, args, index).map_err(exception_text)? {
        Value::Str(text) => Ok(text.as_str().to_owned()),
        value => {
            Err(format!("java.lang.ClassCastException: {}", class_cast(&value, "StringValue")))
        }
    }
}

/// The options of a plain text method, `(RecordValue)` cast, or the text of the exception.
fn options_parameter(ctx: &mut Ctx<'_>, args: &[Arg], index: usize) -> Parameters<Value> {
    let options = forced(ctx, args, index).map_err(exception_text)?;
    match to_record(&options) {
        Some(_) => Ok(options),
        None => {
            Err(format!("java.lang.ClassCastException: {}", class_cast(&options, "RecordValue")))
        }
    }
}

/// `tlc2.overrides.IOUtils#textSerialize`, which writes a string to a file.
fn text_serialize(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome<Option<Value>> {
    let invalid = |exception: String| {
        let message = format!("Serialize error invalid parameters: {exception}");
        Ok(Some(exec_record(1, "", &message)))
    };
    let options = match options_parameter(ctx, args, 2) {
        Ok(options) => options,
        Err(exception) => return invalid(exception),
    };
    if string_option(&options, "format")? != "TXT" {
        return Ok(None);
    }
    let parameters = (|| -> Parameters<_> {
        let payload = string_parameter(ctx, args, 0)?;
        let path = string_parameter(ctx, args, 1)?;
        let open_options = open_option_names(&options).map_err(exception_text)?;
        let charset = string_option(&options, "charset").map_err(exception_text)?;
        Ok((payload, path, open_options, charset))
    })();
    let (payload, path, open_options, charset) = match parameters {
        Ok(parameters) => parameters,
        Err(exception) => return invalid(exception),
    };
    let written = Charset::named(&charset).and_then(|charset| {
        let bytes = charset.encode(&payload)?;
        let mut file = open(&path, &open_options)?;
        file.write_all(&bytes).map_err(|error| java_io_exception(&error, &path))
    });
    Ok(Some(match written {
        Ok(()) => exec_record(0, "Finish writing to the file with success!", ""),
        Err(exception) => {
            exec_record(1, "", &format!("Serialize error writing to the file: {exception}"))
        }
    }))
}

/// `tlc2.overrides.IOUtils#textDeserialize`, which reads a file as a string.
fn text_deserialize(ctx: &mut Ctx<'_>, args: &[Arg]) -> Outcome<Option<Value>> {
    let invalid = |exception: String| {
        let message = format!("Deserialize error invalid parameters: {exception}");
        Ok(Some(exec_record(1, "", &message)))
    };
    let options = match options_parameter(ctx, args, 1) {
        Ok(options) => options,
        Err(exception) => return invalid(exception),
    };
    if string_option(&options, "format")? != "TXT" {
        return Ok(None);
    }
    let parameters = (|| -> Parameters<_> {
        let path = string_parameter(ctx, args, 0)?;
        let charset = string_option(&options, "charset").map_err(exception_text)?;
        Ok((path, charset))
    })();
    let (path, charset) = match parameters {
        Ok(parameters) => parameters,
        Err(exception) => return invalid(exception),
    };
    let read = Charset::named(&charset).and_then(|charset| {
        let bytes = std::fs::read(&path).map_err(|error| java_io_exception(&error, &path))?;
        charset.decode(&bytes)
    });
    Ok(Some(match read {
        Ok(text) => exec_record(0, &text, ""),
        Err(exception) => {
            exec_record(1, "", &format!("Deserialize error reading from the file: {exception}"))
        }
    }))
}

/// The text of the exception `java.nio.file.Files` raises for an operating system error.
fn java_io_exception(error: &std::io::Error, path: &str) -> String {
    use std::io::ErrorKind;
    match error.kind() {
        ErrorKind::NotFound => format!("java.nio.file.NoSuchFileException: {path}"),
        ErrorKind::PermissionDenied => format!("java.nio.file.AccessDeniedException: {path}"),
        ErrorKind::AlreadyExists => format!("java.nio.file.FileAlreadyExistsException: {path}"),
        _ => format!("java.io.IOException: {}", os_message(error)),
    }
}

/// Opens a file for writing with Java's `StandardOpenOption`s, as `Files.newOutputStream` does:
/// it always writes, and creates and truncates the file when no option is given.
fn open(path: &str, names: &[String]) -> Result<std::fs::File, String> {
    let mut options = std::fs::OpenOptions::new();
    options.write(true);
    if names.is_empty() {
        options.create(true).truncate(true);
    }
    let (mut appends, mut truncates) = (false, false);
    for name in names {
        match name.as_str() {
            "APPEND" => {
                appends = true;
                options.append(true);
            }
            "TRUNCATE_EXISTING" => {
                truncates = true;
                options.truncate(true);
            }
            "CREATE" => {
                options.create(true);
            }
            "CREATE_NEW" => {
                options.create_new(true);
            }
            "WRITE" | "READ" | "DELETE_ON_CLOSE" | "SPARSE" | "SYNC" | "DSYNC" => {}
            _ => {
                return Err(format!(
                    "java.lang.IllegalArgumentException: No enum constant java.nio.file.StandardOpenOption.{name}"
                ));
            }
        }
    }
    if names.iter().any(|name| name == "READ") {
        return Err("java.lang.IllegalArgumentException: READ not allowed".to_owned());
    }
    if appends && truncates {
        return Err(
            "java.lang.IllegalArgumentException: APPEND + TRUNCATE_EXISTING not allowed".to_owned()
        );
    }
    options.open(path).map_err(|error| java_io_exception(&error, path))
}

/// The charsets of `Charset.forName` that text files can use.
#[derive(Clone, Copy)]
enum Charset {
    Utf8,
    Ascii,
    Latin1,
}

impl Charset {
    fn named(name: &str) -> Result<Self, String> {
        Ok(match name.to_ascii_uppercase().as_str() {
            "UTF-8" | "UTF8" | "UNICODE-1-1-UTF-8" => Self::Utf8,
            "US-ASCII" | "ASCII" | "ISO646-US" | "US" | "DEFAULT" | "IBM367" | "CP367" => {
                Self::Ascii
            }
            "ISO-8859-1" | "ISO8859-1" | "ISO8859_1" | "ISO_8859_1" | "ISO-LATIN-1" | "LATIN1"
            | "L1" | "8859_1" | "CP819" | "IBM819" => Self::Latin1,
            _ => return Err(format!("java.nio.charset.UnsupportedCharsetException: {name}")),
        })
    }

    fn limit(self) -> Option<u32> {
        match self {
            Self::Utf8 => None,
            Self::Ascii => Some(0x7f),
            Self::Latin1 => Some(0xff),
        }
    }

    fn encode(self, text: &str) -> Result<Vec<u8>, String> {
        let Some(limit) = self.limit() else { return Ok(text.as_bytes().to_vec()) };
        let bytes = text
            .chars()
            .map(|char| u8::try_from(char as u32).ok().filter(|&byte| u32::from(byte) <= limit));
        bytes.collect::<Option<Vec<u8>>>().ok_or_else(|| {
            "java.nio.charset.UnmappableCharacterException: Input length = 1".to_owned()
        })
    }

    fn decode(self, bytes: &[u8]) -> Result<String, String> {
        let malformed = || "java.nio.charset.MalformedInputException: Input length = 1".to_owned();
        match self {
            Self::Utf8 => String::from_utf8(bytes.to_vec()).map_err(|_| malformed()),
            Self::Ascii if bytes.is_ascii() => {
                Ok(bytes.iter().map(|&byte| char::from(byte)).collect())
            }
            Self::Ascii => Err(malformed()),
            Self::Latin1 => Ok(bytes.iter().map(|&byte| char::from(byte)).collect()),
        }
    }
}
