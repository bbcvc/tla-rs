//! Ported from tla-ts `tests/unit/bags.test.ts`.

use std::sync::Arc;

use tla_value::{LazySet, Result, Value};

use crate::native::OperatorKind;
use crate::stdlib::testing::{call, call_in, error, evaluator, int, ints, operator, string, tuple};
use crate::{Arg, Evaluator, Operator};

fn bags(name: &str, args: &[Value]) -> Value {
    call("Bags", name, args).unwrap_or_else(|error| panic!("{name}: {error}"))
}

fn function(pairs: &[(Value, Value)]) -> Value {
    Value::function(pairs.to_vec()).unwrap()
}

fn empty_bag() -> Value {
    bags("EmptyBag", &[])
}

#[test]
fn accepts_the_values_tlcs_java_overrides_accept() {
    let is_a_bag = |value: Value| bags("IsABag", &[value]).as_bool().unwrap();
    assert!(!is_a_bag(Value::model("C")));
    assert!(!is_a_bag(string("abc")));
    assert!(!is_a_bag(ints(&[1])));
    assert!(is_a_bag(tuple(&[1, 2])));
    let difference = bags("\\ominus", &[tuple(&[0, -1, 2]), empty_bag()]);
    assert!(difference.equals(&function(&[(int(3), int(2))])).unwrap());
    assert_eq!(bags("BagUnion", &[ints(&[1])]).as_int(), Some(1));
    let union = bags("BagUnion", &[Value::set(vec![tuple(&[0]), tuple(&[1])]).unwrap()]);
    assert_eq!(union.to_string(), "<<1>>");
    assert_eq!(bags("\\sqsubseteq", &[tuple(&[0]), empty_bag()]).as_bool(), Some(true));
    assert_eq!(bags("\\sqsubseteq", &[tuple(&[1]), tuple(&[-3])]).as_bool(), Some(false));
    assert_eq!(bags("BagIn", &[Value::model("C"), tuple(&[1])]).as_bool(), Some(false));
    assert_eq!(bags("BagIn", &[int(1), tuple(&[0])]).as_bool(), Some(false));
    assert_eq!(bags("CopiesIn", &[int(2), tuple(&[1, 0])]).as_int(), Some(0));
    assert_eq!(bags("CopiesIn", &[int(1), tuple(&[3])]).as_int(), Some(3));
}

#[test]
fn combines_bags() {
    let bag = |elements: &[&str]| {
        let set = Value::set(elements.iter().map(|element| string(element)).collect()).unwrap();
        bags("SetToBag", &[set])
    };
    let sum = bags("\\oplus", &[bag(&["a", "b"]), bag(&["a"])]);
    assert_eq!(bags("CopiesIn", &[string("a"), sum.clone()]).as_int(), Some(2));
    assert_eq!(bags("BagCardinality", std::slice::from_ref(&sum)).as_int(), Some(3));
    assert_eq!(bags("BagToSet", std::slice::from_ref(&sum)).cardinality().unwrap(), 2);
    assert_eq!(bags("BagToSet", &[tuple(&[4, 4])]).to_string(), "1..2");
    assert_eq!(bags("SetToBag", &[Value::Interval(1, 3)]).to_string(), "<<1, 1, 1>>");
    let sub_bags = bags("SubBag", &[sum]);
    assert_eq!(sub_bags.cardinality().unwrap(), 6);
    assert!(sub_bags.contains(&bag(&["a", "b"])).unwrap());
    assert_eq!(bags("SubBag", &[tuple(&[2, 1, 3])]).cardinality().unwrap(), 24);
    assert_eq!(bags("SubBag", &[empty_bag()]).to_string(), "{<<>>}");
    assert_eq!(
        bags("SubBag", &[tuple(&[2, 1])]).to_string(),
        "{<<>>, <<1>>, <<2>>, (2 :> 1), <<1, 1>>, <<2, 1>>}"
    );
}

#[test]
fn rejects_what_tlc_rejects() {
    let cases = [
        (
            "BagCardinality",
            vec![tuple(&[0])],
            "Applying BagCardinality to the following value,\nwhich is not a bag:\n<<0>>",
        ),
        (
            "\\oplus",
            vec![tuple(&[0]), empty_bag()],
            "The first argument of (+) should be a bag, but instead it is:\n<<0>>",
        ),
        (
            "\\ominus",
            vec![empty_bag(), int(1)],
            "The second argument of (-) should be a bag, but instead it is:\n1",
        ),
        (
            "BagIn",
            vec![int(1), Value::tuple(vec![string("a")])],
            "The second argument of BagIn should be a bag, but instead it is:\n<<\"a\">>",
        ),
        (
            "BagUnion",
            vec![ints(&[1, 2])],
            "Attempted to apply BagUnion to the following set, whose\nelement is not a bag:\n{1, 2}",
        ),
        (
            "BagUnion",
            vec![Value::lazy(LazySet::Nat)],
            "Applying BagUnion to the following value,\nwhich is not a finite enumerable set:\nNat",
        ),
        (
            "SetToBag",
            vec![Value::lazy(LazySet::Nat)],
            "Applying BagToSet to the following value,\nwhich is not a function with a finite domain:\nNat",
        ),
        (
            "\\sqsubseteq",
            vec![int(1), empty_bag()],
            "Applying \\sqsubseteq to the following value,\nwhich is not a function with a finite domain:\n1",
        ),
        ("\\oplus", vec![tuple(&[i32::MAX]), tuple(&[1])], "Overflow when computing 2147483647+1"),
        (
            "SubBag",
            vec![Value::tuple(vec![string("a")])],
            "The first argument of > should be an integer, but instead it is:\n\"a\"",
        ),
    ];
    for (name, args, message) in cases {
        assert_eq!(error("Bags", name, &args), message, "{name}");
    }
    let args = vec![Arg::Value(Value::tuple(vec![string("a")]))];
    assert_eq!(
        call_in(&evaluator(), "Bags", "SubBag", true, args).unwrap_err().0,
        "The first argument of >= should be an integer, but instead it is:\n\"a\""
    );
    assert!(call("Bags", "SubBag", &[tuple(&[0])]).is_err());
}

fn cast_error(method: &str) -> String {
    format!(
        "Attempted to apply the operator overridden by the Java method\npublic static {method}(tlc2.value.impl.Value,tlc2.value.impl.Value),\nbut it produced the following error:\nclass tlc2.value.impl.StringValue cannot be cast to class tlc2.value.impl.IntValue (tlc2.value.impl.StringValue and tlc2.value.impl.IntValue are in unnamed module of loader 'app')"
    )
}

fn bag_of_all(evaluator: &Evaluator, operator: Arg, bag: Value) -> Result<Value> {
    call_in(evaluator, "Bags", "BagOfAll", false, vec![operator, Arg::Value(bag)])
}

#[test]
fn fails_to_cast_a_count_that_isnt_an_integer() {
    let strings = Value::tuple(vec![string("a")]);
    assert_eq!(
        error("Bags", "\\ominus", &[strings.clone(), empty_bag()]),
        cast_error("tlc2.value.impl.Value tlc2.module.Bags.BagDiff")
    );
    assert_eq!(
        error("Bags", "\\sqsubseteq", &[strings, empty_bag()]),
        cast_error("tlc2.value.IBoolValue tlc2.module.Bags.SqSubseteq")
    );
    let counts = Value::tuple(vec![string("a"), int(1)]);
    let constant = operator(|_| Ok(Value::TRUE));
    assert_eq!(
        bag_of_all(&evaluator(), constant, counts).unwrap_err().0,
        cast_error("tlc2.value.impl.Value tlc2.module.Bags.BagOfAll")
    );
}

#[test]
fn applies_an_operator_to_each_element() {
    let half = operator(|args| Ok(Value::Int(args[0].as_int().unwrap() / 2)));
    let all = bag_of_all(&evaluator(), half, tuple(&[1, 2, 3, 4])).unwrap();
    let expected = function(&[(int(0), int(1)), (int(1), int(5)), (int(2), int(4))]);
    assert!(all.equals(&expected).unwrap());
    let constant = operator(|_| Ok(Value::TRUE));
    let all = bag_of_all(&evaluator(), constant, tuple(&[1])).unwrap();
    assert!(all.equals(&function(&[(Value::TRUE, int(1))])).unwrap());
    assert_eq!(
        bag_of_all(&evaluator(), operator(|_| Ok(Value::TRUE)), int(1)).unwrap_err().0,
        "The second argument of BagOfAll should be a function with a finite domain, but instead it is:\n1"
    );
}

#[test]
fn rejects_an_operator_whose_body_is_a_literal() {
    let source = "---- MODULE T ----\nH(e) == \"c\"\nG(e) == 1\nK(e) == e\n====\n";
    let spec = tla_resolve::resolve(source, &mut |_: &str| None).unwrap();
    let evaluator = Evaluator::new(Arc::new(spec), Vec::new());
    let definition = |name: &str| {
        let Some(tla_resolve::RootName::Def(def)) = evaluator.spec().lookup(name) else {
            panic!("{name} is a definition")
        };
        Arg::Op(Operator(OperatorKind::Def { def, parent: None }))
    };
    assert_eq!(
        bag_of_all(&evaluator, definition("H"), tuple(&[1])).unwrap_err().0,
        "The first argument of BagOfAll should be an operator, but instead it is:\n\"c\""
    );
    assert_eq!(
        bag_of_all(&evaluator, definition("G"), tuple(&[1])).unwrap_err().0,
        "The first argument of BagOfAll should be an operator, but instead it is:\n1"
    );
}
