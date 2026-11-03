//! Ported from tla-ts's Json fixtures `JsonTests.tla` and `JsonValues.tla`.

use std::sync::atomic::{AtomicUsize, Ordering};

use tla_value::{LazySet, Symbol, Value};

use super::{json_integer, parse_json};
use crate::stdlib::testing::{call, error, int, ints, string, tuple};

fn json(name: &str, value: Value) -> String {
    match call("Json", name, &[value]).unwrap() {
        Value::Str(text) => text.as_str().to_owned(),
        value => panic!("{name} returned {value}"),
    }
}

fn record(fields: &[(&str, Value)]) -> Value {
    Value::record(
        fields.iter().map(|(name, value)| (Symbol::intern(name), value.clone())).collect(),
    )
}

#[test]
fn converts_values_like_tlc() {
    assert_eq!(json("ToJsonArray", Value::empty_set()), "[]");
    assert_eq!(json("ToJsonArray", tuple(&[])), "[]");
    assert_eq!(json("ToJson", Value::FALSE), "false");
    assert_eq!(json("ToJson", int(1)), "1");
    assert_eq!(json("ToJson", string("a")), "\"a\"");
    assert_eq!(json("ToJson", Value::model("ModelValue")), "\"ModelValue\"");
    assert_eq!(
        json("ToJson", Value::set(vec![Value::TRUE, Value::FALSE]).unwrap()),
        "[false,true]"
    );
    assert_eq!(json("ToJson", ints(&[3, 2, 1])), "[1,2,3]");
    assert_eq!(json("ToJson", tuple(&[3, 2, 1])), "[3,2,1]");
    assert_eq!(json("ToJson", Value::Interval(1, 3)), "[1,2,3]");
    let functions = Value::lazy(LazySet::FuncSet { domain: ints(&[1, 0]), range: ints(&[5]) });
    assert_eq!(json("ToJson", functions), "[{\"0\":5,\"1\":5}]");
    assert_eq!(json("ToJson", Value::lazy(LazySet::Subset(ints(&[2, 1])))), "[[],[1],[2],[1,2]]");
    let object = record(&[
        ("a", Value::set(vec![tuple(&[1, 2])]).unwrap()),
        ("b", record(&[("c", int(3))])),
    ]);
    let text = json("ToJsonObject", object);
    assert!(text == "{\"a\":[[1,2]],\"b\":{\"c\":3}}" || text == "{\"b\":{\"c\":3},\"a\":[[1,2]]}");
    let negative = Value::function(vec![(int(-1), int(-1)), (int(2), int(2))]).unwrap();
    assert_eq!(json("ToJson", negative), "{\"-1\":-1,\"2\":2}");
    let sparse = Value::function(vec![(int(2), int(2)), (int(3), int(3))]).unwrap();
    assert_eq!(json("ToJsonArray", sparse), "{\"2\":2,\"3\":3}");
    assert_eq!(json("ToJson", string("a\"\n\u{1}\u{2028}")), "\"a\\\"\\n\\u0001\\u2028\"");
}

fn java(method: &str, message: &str) -> String {
    format!(
        "Attempted to apply the operator overridden by the Java method\npublic static {method},\nbut it produced the following error:\n{message}"
    )
}

#[test]
fn rejects_what_tlc_rejects() {
    assert_eq!(
        error("Json", "ToJsonArray", &[record(&[("a", int(1))])]),
        java(
            "tlc2.value.impl.StringValue tlc2.module.Json.toJsonArray(tlc2.value.IValue) throws java.io.IOException",
            "Cannot convert value: unsupported value type tlc2.value.impl.RecordValue"
        )
    );
    assert_eq!(
        error("Json", "ToJsonArray", &[int(42)]),
        java(
            "tlc2.value.impl.StringValue tlc2.module.Json.toJsonArray(tlc2.value.IValue) throws java.io.IOException",
            "Cannot convert value: unsupported value type tlc2.value.impl.IntValue"
        )
    );
    assert_eq!(
        error("Json", "ToJsonObject", &[ints(&[1])]),
        java(
            "tlc2.value.impl.StringValue tlc2.module.Json.toJsonObject(tlc2.value.IValue) throws java.io.IOException",
            "Cannot convert value: unsupported value type tlc2.value.impl.SetEnumValue"
        )
    );
    assert_eq!(
        error("Json", "ToJson", &[Value::lazy(LazySet::Nat)]),
        java(
            "tlc2.value.impl.StringValue tlc2.module.Json.toJson(tlc2.value.IValue) throws java.io.IOException",
            "Cannot convert value: unsupported value type tlc2.value.impl.UserValue"
        )
    );
    assert_eq!(
        error("Json", "JsonSerialize", &[int(42), tuple(&[1])]),
        java(
            "synchronized tlc2.value.impl.BoolValue tlc2.module.Json.serialize(tlc2.value.impl.StringValue,tlc2.value.impl.Value) throws java.io.IOException",
            "Cannot cast tlc2.value.impl.IntValue to tlc2.value.impl.StringValue"
        )
    );
    assert_eq!(
        error("Json", "JsonSerialize", &[string("Unwritten.json"), ints(&[1, 2, 3])]),
        "The second argument of JsonSerialize should be a sequence or record, but instead it is:\n{1, 2, 3}"
    );
    assert_eq!(
        error("Json", "JsonDeserialize", &[string("Missing.json")]),
        java(
            "tlc2.value.IValue tlc2.module.Json.deserialize(tlc2.value.impl.StringValue) throws java.io.IOException",
            "Missing.json (No such file or directory)"
        )
    );
}

#[test]
fn reads_numbers_as_gson_does() {
    let numbers =
        ["1", "-2", "1.5", "-1.5", "1e3", "3000000000", "12345678901234567890", "0.0", "2.5e-3"];
    let values: Vec<i32> = numbers.iter().map(|number| json_integer(number)).collect();
    assert_eq!(values, [1, -2, 1, -1, 1000, -1294967296, -350287150, 0, 0]);
    assert_eq!(json_integer("1e40"), 0);
    let parsed = parse_json("[1, -2, 1.5, 1e3]", "method").ok().unwrap();
    assert_eq!(parsed.to_string(), "<<1, -2, 1, 1000>>");
}

#[test]
fn reads_json_values() {
    let parse = |text: &str| parse_json(text, "method").ok().unwrap().to_string();
    assert_eq!(parse("{\"a\": true}"), "[a |-> TRUE]");
    assert_eq!(parse("  [2, \"x\\u0041\\n\"]  "), "<<2, \"xA\\n\">>");
    assert_eq!(parse("{\"k\": 1, \"k\": 2}"), "[k |-> 2]");
    assert_eq!(parse("[]"), "<<>>");
    let empty = parse_json(" ", "M").err().unwrap().into_error().0;
    assert!(empty.ends_with("Cannot convert value: unsupported JSON value null"));
    for invalid in ["[1,]", "{1: 2}", "01", "\"a", "[1] x", "tru"] {
        assert!(parse_json(invalid, "M").is_err(), "{invalid}");
    }
}

#[test]
fn writes_and_reads_files() {
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir();
    let name =
        format!("tla-rs-json-{}-{}", std::process::id(), COUNTER.fetch_add(1, Ordering::SeqCst));
    let path = directory.join(name);
    let path_value = string(path.to_str().unwrap());
    let rows = Value::tuple(vec![
        record(&[("a", int(1)), ("b", string("a"))]),
        record(&[("a", int(2)), ("b", string("b"))]),
    ]);
    let written = call("Json", "ndJsonSerialize", &[path_value.clone(), rows.clone()]).unwrap();
    assert_eq!(written.as_bool(), Some(true));
    let read = call("Json", "ndJsonDeserialize", std::slice::from_ref(&path_value)).unwrap();
    assert!(read.equals(&rows).unwrap());
    let nested = record(&[("a", int(3)), ("b", record(&[("c", tuple(&[4, 5, 6]))]))]);
    call("Json", "JsonSerialize", &[path_value.clone(), nested.clone()]).unwrap();
    let read = call("Json", "JsonDeserialize", std::slice::from_ref(&path_value)).unwrap();
    assert!(read.equals(&nested).unwrap());
    std::fs::remove_file(path).unwrap();
}
