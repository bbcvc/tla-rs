//! Tests of IOUtils' natives. The commands they run are `sh -c 'printf ...'`.

use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use tla_tools_resolve::RootName;
use tla_tools_value::{Result, Symbol, Value};

use super::process::java_format;
use crate::stdlib::testing::{evaluator, int, string};
use crate::{Arg, Ctx, Evaluator};

/// The definitions of CommunityModules' IOUtils.tla that the tests use, verbatim.
const IO_UTILS: &str = r#"
---- MODULE IOUtils ----
LOCAL INSTANCE TLC
LOCAL INSTANCE Integers
IOSerialize(val, absoluteFilename, compress) == TRUE
IODeserialize(absoluteFilename, compressed) == CHOOSE val : TRUE
Serialize(value, dest, options) ==
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE
Deserialize(src, options) ==
  CHOOSE val : TRUE
IOExec(command) ==
  CHOOSE r \in [exitValue : Int, stdout : STRING, stderr : STRING] : TRUE
IOEnv ==
  CHOOSE r \in [STRING -> STRING] : TRUE
atoi(str) ==
  CHOOSE i \in Int : ToString(i) = str
====
"#;

/// Calls the CommunityModules native of `name` with `args`.
fn call_with(evaluator: &Evaluator, name: &str, args: Vec<Arg>) -> Result<Value> {
    let native = crate::stdlib::lookup_community("IOUtils", name)
        .unwrap_or_else(|| panic!("IOUtils!{name} has no native"));
    native(&mut Ctx::new(evaluator, None), &args)
}

fn call(name: &str, args: &[Value]) -> Result<Value> {
    call_with(&evaluator(), name, args.iter().cloned().map(Arg::Value).collect())
}

fn error(name: &str, args: &[Value]) -> String {
    call(name, args).expect_err("the native fails").0
}

fn field(record: &Value, name: &str) -> Value {
    record.field(Symbol::intern(name)).unwrap()
}

fn strings(parts: &[&str]) -> Value {
    Value::tuple(parts.iter().map(|part| string(part)).collect())
}

/// A path in the temporary directory that no other test uses.
fn temporary_path(name: &str) -> PathBuf {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let count = COUNTER.fetch_add(1, Ordering::SeqCst);
    std::env::temp_dir().join(format!("tla-rs-io-{}-{count}-{name}", std::process::id()))
}

/// The value of `E == expression` in a module extending IOUtils, with the CommunityModules'
/// natives if `is_community`.
fn evaluate(expression: &str, is_community: bool) -> Result<Value> {
    let source = format!("---- MODULE T ----\nEXTENDS IOUtils, TLC\nE == {expression}\n====\n");
    let mut loader = |name: &str| (name == "IOUtils").then(|| IO_UTILS.to_owned());
    let spec = tla_tools_resolve::resolve(&source, &mut loader).unwrap();
    let mut evaluator = Evaluator::new(Arc::new(spec), Vec::new());
    if is_community {
        evaluator = evaluator.with_community_modules();
    }
    let Some(RootName::Def(def)) = evaluator.spec().lookup("E") else { panic!("E is defined") };
    evaluator.eval_def(def, None).map_err(|error| tla_tools_value::Error(error.message))
}

const JAVA: &str = "Attempted to apply the operator overridden by the Java method\n";

#[test]
fn reports_the_environment_as_a_record() {
    let evaluator = evaluator();
    let variables = [("JSON", "trace.ndjson"), ("a.b", "1")];
    evaluator.runtime().set_environment(variables.map(|(name, value)| (name.into(), value.into())));
    let environment = call_with(&evaluator, "IOEnv", Vec::new()).unwrap();
    assert_eq!(field(&environment, "JSON").to_string(), "\"trace.ndjson\"");
    assert_eq!(environment.apply(&string("a.b")).unwrap().to_string(), "\"1\"");
    assert!(!environment.domain().unwrap().contains(&string("TRACE")).unwrap());
    // The process's own environment, read once.
    let process = call("IOEnv", &[]).unwrap();
    assert!(process.domain().unwrap().is_set());
}

#[test]
fn reads_integers_as_java_does() {
    let atoi = |text: &str| call("atoi", &[string(text)]).map(|value| value.as_int());
    assert_eq!(atoi("42"), Ok(Some(42)));
    assert_eq!(atoi("-17"), Ok(Some(-17)));
    assert_eq!(atoi("+5"), Ok(Some(5)));
    assert_eq!(atoi("-2147483648"), Ok(Some(i32::MIN)));
    for invalid in ["2147483648", "abc", "", "-", "1.5", " 1"] {
        assert!(atoi(invalid).is_err(), "{invalid:?}");
    }
    assert_eq!(
        error("atoi", &[string("abc")]),
        "The argument of atoi should be a string, but instead it is:\n\"abc\""
    );
    assert_eq!(
        error("atoi", &[int(1)]),
        "The argument of atoi should be a string, but instead it is:\n1"
    );
}

#[test]
fn runs_no_command_unless_the_runtime_allows_it() {
    assert_eq!(
        error("IOExec", &[strings(&["ls", "/"])]),
        "IOExec would run the command <<\"ls\", \"/\">>, but running commands is off: Runtime::allow_exec turns it on"
    );
    let environment = Value::record(vec![(Symbol::intern("X"), int(1))]);
    assert!(
        error("IOEnvExec", &[environment, strings(&["ls"])]).starts_with("IOEnvExec would run")
    );
    assert!(
        error("IOExecTemplate", &[strings(&["%s"]), strings(&["ls"])])
            .starts_with("IOExecTemplate would run the command <<\"ls\">>")
    );
}

#[test]
fn checks_the_arguments_of_commands_as_ioutils_does() {
    assert_eq!(
        error("IOExec", &[string("ls")]),
        "The argument of IOExec should be a sequence, but instead it is:\n\"ls\""
    );
    assert_eq!(
        error("IOExec", &[Value::tuple(vec![string("ls"), int(1)])]),
        "The argument of IOExec should be a sequence, but instead it is:\n1"
    );
    assert_eq!(
        error("IOEnvExec", &[int(1), strings(&["ls"])]),
        "The argument of IOEnvExec should be a record, but instead it is:\n1"
    );
    assert_eq!(
        error("IOExecTemplate", &[strings(&["%s"]), string("x")]),
        "The argument of IOExecTemplate should be a sequence, but instead it is:\n\"x\""
    );
    assert!(
        error("IOExecTemplate", &[strings(&["%s %s"]), strings(&["a"])])
            .ends_with("but it produced the following error:\nFormat specifier '%s'")
    );
}

#[cfg(unix)]
fn exec(name: &str, args: &[Value]) -> Value {
    let evaluator = evaluator();
    evaluator.runtime().allow_exec(true);
    call_with(&evaluator, name, args.iter().cloned().map(Arg::Value).collect()).unwrap()
}

#[cfg(unix)]
#[test]
fn runs_commands_when_allowed() {
    let result = exec("IOExec", &[strings(&["sh", "-c", "printf out; printf err >&2; exit 3"])]);
    assert_eq!(result.to_string(), "[exitValue |-> 3, stdout |-> \"out\", stderr |-> \"err\"]");
    let environment = Value::record(vec![
        (Symbol::intern("A"), string("text")),
        (Symbol::intern("B"), Value::set(vec![int(2), int(1)]).unwrap()),
    ]);
    let result =
        exec("IOEnvExec", &[environment, strings(&["sh", "-c", "printf '%s|%s' \"$A\" \"$B\""])]);
    assert_eq!(field(&result, "stdout").to_string(), "\"text|{1, 2}\"");
    let result =
        exec("IOExecTemplate", &[strings(&["sh", "-c", "printf %2$s%1$s"]), strings(&["b", "a"])]);
    assert_eq!(field(&result, "stdout").to_string(), "\"ab\"");
    let evaluator = evaluator();
    evaluator.runtime().allow_exec(true);
    let missing =
        call_with(&evaluator, "IOExec", vec![Arg::Value(strings(&["tla-rs-no-such-program"]))]);
    assert_eq!(
        missing.unwrap_err().0,
        format!(
            "{JAVA}public static tlc2.value.impl.Value tlc2.overrides.IOUtils.ioExec(tlc2.value.impl.Value) throws java.io.IOException,java.lang.InterruptedException,\nbut it produced the following error:\nCannot run program \"tla-rs-no-such-program\": error=2, No such file or directory"
        )
    );
}

#[test]
fn formats_templates_as_java_does() {
    let format = |template: &str, arguments: &[&str]| {
        let arguments: Vec<String> =
            arguments.iter().map(|argument| argument.to_string()).collect();
        java_format(template, &arguments)
    };
    assert_eq!(format("ls %s %s", &["-lah", "/tmp"]).unwrap(), "ls -lah /tmp");
    assert_eq!(format("%2$s %1$s %<s", &["a", "b"]).unwrap(), "b a a");
    assert_eq!(format("[%-4s][%4s][%.1s]", &["ab", "cd", "ef"]).unwrap(), "[ab  ][  cd][e]");
    assert_eq!(format("%S%b%% done%n", &["up", "x"]).unwrap(), "UPtrue% done\n");
    assert_eq!(format("%h", &["a"]).unwrap(), "61");
    assert_eq!(format("plain", &["unused"]).unwrap(), "plain");
    assert_eq!(format("%s %s", &["a"]).unwrap_err(), "Format specifier '%s'");
    assert_eq!(format("%3$s", &["a"]).unwrap_err(), "Format specifier '%3$s'");
    assert_eq!(format("%d", &["1"]).unwrap_err(), "d != java.lang.String");
    assert_eq!(format("%q", &["1"]).unwrap_err(), "Conversion = 'q'");
    assert_eq!(format("50%", &[]).unwrap_err(), "Conversion = '%'");
    assert_eq!(format("%#s", &["a"]).unwrap_err(), "Conversion = s, Flags = #");
    assert_eq!(format("%-s", &["a"]).unwrap_err(), "%-s");
}

/// A TLA+ string literal for a path.
fn literal(path: &std::path::Path) -> String {
    format!("{:?}", path.to_str().unwrap())
}

#[test]
fn writes_ndjson_with_tlcs_json_class_whatever_the_class_path() {
    let path = temporary_path("lines.ndjson");
    let options = r#"[format |-> "NDJSON", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]"#;
    for is_community in [false, true] {
        let written = evaluate(
            &format!("Serialize(<<[a |-> 1], <<2, \"x\">>>>, {}, {options})", literal(&path)),
            is_community,
        );
        assert_eq!(written.unwrap().as_bool(), Some(true));
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "{\"a\":1}\n[2,\"x\"]\n");
    }
    let appended = evaluate(
        &format!(
            r#"Serialize(<<3>>, {}, [format |-> "NDJSON", charset |-> "UTF-8", openOptions |-> <<"APPEND">>])"#,
            literal(&path)
        ),
        false,
    );
    assert_eq!(appended.unwrap().as_bool(), Some(true));
    assert_eq!(std::fs::read_to_string(&path).unwrap(), "{\"a\":1}\n[2,\"x\"]\n3\n");
    std::fs::remove_file(&path).unwrap();
    let failed = evaluate(
        r#"Serialize(<<1>>, "f", [format |-> "NDJSON", charset |-> "UTF-8", openOptions |-> <<"WRITEA">>])"#,
        false,
    );
    assert!(failed.unwrap_err().0.ends_with(
        "but it produced the following error:\njava.lang.IllegalArgumentException: No enum constant java.nio.file.StandardOpenOption.WRITEA"
    ));
}

#[test]
fn falls_back_to_the_tla_definition_for_other_formats() {
    let expression =
        r#"Serialize("text", "f", [format |-> "TXT", charset |-> "UTF-8", openOptions |-> <<>>])"#;
    let failure = evaluate(expression, false).unwrap_err().0;
    assert!(failure.starts_with(&format!(
        "{JAVA}public static synchronized tlc2.value.impl.Value tlc2.module.Json.textSerialize("
    )));
    assert!(failure.contains("exitValue"), "{failure}");
    let expression =
        r#"Serialize("text", "f", [format |-> "XML", charset |-> "UTF-8", openOptions |-> <<>>])"#;
    let failure = evaluate(expression, true).unwrap_err().0;
    assert!(failure.starts_with(&format!(
        "{JAVA}public static synchronized tlc2.value.impl.Value tlc2.overrides.IOUtils.textSerialize("
    )));
    let failure = evaluate(r#"Deserialize("f", [format |-> "XML", charset |-> "UTF-8"])"#, true);
    assert!(failure.unwrap_err().0.contains("tlc2.overrides.IOUtils.textDeserialize("));
}

#[test]
fn reads_and_writes_text_with_communitymodules_ioutils() {
    let path = temporary_path("text.txt");
    let options = r#"[format |-> "TXT", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]"#;
    let written =
        evaluate(&format!("Serialize(\"caf\u{e9}\", {}, {options})", literal(&path)), true);
    let written = written.unwrap();
    assert_eq!(field(&written, "exitValue").as_int(), Some(0));
    assert_eq!(
        field(&written, "stdout").to_string(),
        "\"Finish writing to the file with success!\""
    );
    let read = evaluate(
        &format!(r#"Deserialize({}, [format |-> "TXT", charset |-> "UTF-8"])"#, literal(&path)),
        true,
    );
    assert_eq!(
        read.unwrap().to_string(),
        "[exitValue |-> 0, stdout |-> \"caf\u{e9}\", stderr |-> \"\"]"
    );
    std::fs::remove_file(&path).unwrap();
    let missing = evaluate(
        &format!(r#"Deserialize({}, [format |-> "TXT", charset |-> "UTF-8"])"#, literal(&path)),
        true,
    );
    assert_eq!(
        field(&missing.unwrap(), "stderr").to_string(),
        format!(
            "\"Deserialize error reading from the file: java.nio.file.NoSuchFileException: {}\"",
            path.display()
        )
    );
    let invalid = evaluate(&format!("Serialize(42, {}, {options})", literal(&path)), true).unwrap();
    assert_eq!(field(&invalid, "exitValue").as_int(), Some(1));
    assert!(field(&invalid, "stderr").to_string().starts_with(
        "\"Serialize error invalid parameters: java.lang.ClassCastException: class tlc2.value.impl.IntValue cannot be cast to class tlc2.value.impl.StringValue"
    ));
    let ascii = r#"[format |-> "TXT", charset |-> "US-ASCII", openOptions |-> <<"CREATE_NEW">>]"#;
    let unmappable =
        evaluate(&format!("Serialize(\"\u{e9}\", {}, {ascii})", literal(&path)), true).unwrap();
    assert_eq!(
        field(&unmappable, "stderr").to_string(),
        "\"Serialize error writing to the file: java.nio.charset.UnmappableCharacterException: Input length = 1\""
    );
    assert!(!path.exists());
}

#[test]
fn refuses_javas_object_serialization() {
    assert_eq!(
        error("IOSerialize", &[int(1), string("f.vos"), Value::FALSE]),
        "IOSerialize writes Java's object serialization format, which is not supported"
    );
    let missing = temporary_path("missing.vos");
    assert_eq!(
        error("IODeserialize", &[string(missing.to_str().unwrap()), Value::FALSE]),
        format!(
            "{JAVA}public static final tlc2.value.IValue tlc2.overrides.IOUtils.ioDeserialize(tlc2.value.impl.StringValue,tlc2.value.impl.BoolValue) throws java.io.IOException,\nbut it produced the following error:\n{} (No such file or directory)",
            missing.display()
        )
    );
    let present = temporary_path("present.vos");
    std::fs::write(&present, b"\xac\xed").unwrap();
    assert_eq!(
        error("IODeserialize", &[string(present.to_str().unwrap()), Value::FALSE]),
        "IODeserialize reads Java's object serialization format, which is not supported"
    );
    std::fs::remove_file(&present).unwrap();
    assert!(
        error("IODeserialize", &[int(1), Value::FALSE])
            .ends_with("Cannot cast tlc2.value.impl.IntValue to tlc2.value.impl.StringValue")
    );
}

#[test]
fn uses_the_tla_placeholders_without_communitymodules() {
    let placeholder = evaluate("IOEnv", false).unwrap_err().0;
    assert!(placeholder.contains("STRING"), "{placeholder}");
    assert!(evaluate("\"JSON\" \\in DOMAIN IOEnv", true).unwrap().as_bool().is_some());
    assert_eq!(evaluate("atoi(\"7\")", true).unwrap().as_int(), Some(7));
}
