//! Naturals and Integers: TLC's 32-bit arithmetic, ported from tla-ts `builtins.ts` and
//! `standard-modules.ts`.
//!
//! TLC implements the arithmetic of Naturals with the Java methods of `tlc2.module.Naturals`, or
//! with those of `tlc2.module.Integers` when the spec loads Integers anywhere. The two differ in
//! how `\div` rounds and overflows, in how `\geq` names itself in errors, and in the method an
//! error names.

use tla_value::{LazySet, Value};

use super::{Failure, Outcome, arg, java_class, java_error};
use crate::{Arg, Ctx, Native};

/// The operators of Naturals, with the Java methods of Integers if `$integers`.
macro_rules! arithmetic {
    ($integers:literal, $name:expr) => {
        match $name {
            "Nat" => Some(native!(|_: &mut Ctx<'_>, _: &[Arg]| -> Outcome {
                Ok(Value::lazy(LazySet::Nat))
            })),
            "+" => Some(native!(plus::<$integers>)),
            "-" => Some(native!(minus::<$integers>)),
            "*" => Some(native!(times::<$integers>)),
            "^" => Some(native!(power::<$integers>)),
            "\\div" => Some(native!(divide::<$integers>)),
            "%" => Some(native!(modulo::<$integers>)),
            ".." => Some(native!(interval::<$integers>)),
            "<" => Some(native!(less)),
            ">" => Some(native!(greater)),
            "\\leq" => Some(native!(at_most)),
            "\\geq" => Some(native!(at_least::<$integers>)),
            _ => None,
        }
    };
}

pub(super) fn lookup(name: &str, uses_integers: bool) -> Option<Native> {
    if uses_integers { arithmetic!(true, name) } else { arithmetic!(false, name) }
}

pub(super) fn lookup_integers(name: &str) -> Option<Native> {
    Some(match name {
        "Int" => native!(|_: &mut Ctx<'_>, _: &[Arg]| -> Outcome { Ok(Value::lazy(LazySet::Int)) }),
        "-." => native!(negate),
        _ => return None,
    })
}

fn module_name(integers: bool) -> &'static str {
    if integers { "Integers" } else { "Naturals" }
}

/// A Java method of TLC's arithmetic as `java.lang.reflect.Method` prints it.
fn signature(integers: bool, method: &str, result: &str, arity: usize) -> String {
    let parameters = vec!["tlc2.value.impl.IntValue"; arity].join(",");
    let module = module_name(integers);
    format!("public static tlc2.value.impl.{result} tlc2.module.{module}.{method}({parameters})")
}

/// The integer a Java method that takes an `IntValue` gets, or the failure of its cast.
fn java_integer(value: &Value, signature: impl Fn() -> String) -> Outcome<i32> {
    match value {
        Value::Int(value) => Ok(*value),
        _ => Err(Failure::Eval(java_error(
            &signature(),
            &format!(
                "Cannot cast tlc2.value.impl.{} to tlc2.value.impl.IntValue",
                java_class(value)
            ),
        ))),
    }
}

fn overflow(computation: impl std::fmt::Display) -> Failure {
    Failure::Module(tla_value::Error(format!("Overflow when computing {computation}")))
}

/// Applies an infix operator to two integers with TLC's overflow check.
fn binary<const INTEGERS: bool>(
    args: &[Arg],
    name: &str,
    method: &str,
    compute: impl Fn(i64, i64) -> Outcome<i64>,
) -> Outcome {
    let signature = || signature(INTEGERS, method, "IntValue", 2);
    let left = java_integer(arg(args, 0)?, signature)?;
    let right = java_integer(arg(args, 1)?, signature)?;
    let result = compute(i64::from(left), i64::from(right))?;
    i32::try_from(result).map(Value::Int).map_err(|_| overflow(format!("{left}{name}{right}")))
}

fn plus<const INTEGERS: bool>(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    binary::<INTEGERS>(args, "+", "Plus", |left, right| Ok(left + right))
}

fn minus<const INTEGERS: bool>(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    binary::<INTEGERS>(args, "-", "Minus", |left, right| Ok(left - right))
}

fn times<const INTEGERS: bool>(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    binary::<INTEGERS>(args, "*", "Times", |left, right| Ok(left * right))
}

fn power<const INTEGERS: bool>(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    binary::<INTEGERS>(args, "^", "Expt", |base, exponent| {
        if exponent < 0 {
            fail!(
                "The second argument of ^ should be a natural number, but instead it is:\n{exponent}"
            );
        }
        if base == 0 && exponent == 0 {
            fail!("0^0 is undefined.");
        }
        Ok(match base {
            0 | 1 => base,
            -1 => {
                if exponent % 2 == 0 {
                    1
                } else {
                    -1
                }
            }
            // Any other base leaves the 32-bit range within 32 multiplications, so the result
            // saturates instead of looping over a large exponent.
            _ => {
                let mut result: i64 = 1;
                for _ in 0..exponent.min(33) {
                    result = result.saturating_mul(base);
                }
                result
            }
        })
    })
}

fn divide<const INTEGERS: bool>(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    binary::<INTEGERS>(args, "\\div", "Divide", |left, right| {
        if right == 0 {
            fail!("The second argument of \\div is 0.");
        }
        if !INTEGERS {
            // tlc2.module.Naturals#Divide floors only a quotient Java truncates below 0, and lets
            // -2147483648 \div -1 overflow.
            let (left, right) = (left as i32, right as i32);
            let truncated = left.wrapping_div(right);
            let is_inexact = truncated.wrapping_mul(right) != left;
            return Ok(i64::from(truncated) - i64::from(truncated < 0 && is_inexact));
        }
        let quotient = left.div_euclid(right) - i64::from(right < 0 && left.rem_euclid(right) != 0);
        if i32::try_from(quotient).is_err() {
            return Err(overflow(format!("{left} \\div {right}")));
        }
        Ok(quotient)
    })
}

fn modulo<const INTEGERS: bool>(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    binary::<INTEGERS>(args, "%", "Mod", |left, right| {
        if right <= 0 {
            fail!(
                "The second argument of % should be a positive number, but instead it is:\n{right}"
            );
        }
        Ok(left.rem_euclid(right))
    })
}

fn interval<const INTEGERS: bool>(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let signature = || signature(INTEGERS, "DotDot", "IntervalValue", 2);
    let low = java_integer(arg(args, 0)?, signature)?;
    let high = java_integer(arg(args, 1)?, signature)?;
    Ok(Value::Interval(low, high))
}

/// Compares two integers, failing for another value as the Java method `name` does.
fn compare(args: &[Arg], name: &str, holds: fn(i32, i32) -> bool) -> Outcome {
    let integer = |index: usize, position: &str| -> Outcome<i32> {
        match arg(args, index)? {
            Value::Int(value) => Ok(*value),
            value => fail!(
                "The {position} argument of {name} should be an integer, but instead it is:\n{value}"
            ),
        }
    };
    let left = integer(0, "first")?;
    let right = integer(1, "second")?;
    Ok(Value::Bool(holds(left, right)))
}

fn less(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    compare(args, "<", |left, right| left < right)
}

fn greater(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    compare(args, ">", |left, right| left > right)
}

fn at_most(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    compare(args, "<=", |left, right| left <= right)
}

/// `\geq`. tlc2.module.Naturals#GEQ names itself `>` in its errors.
fn at_least<const INTEGERS: bool>(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    compare(args, if INTEGERS { ">=" } else { ">" }, |left, right| left >= right)
}

/// Integers' prefix `-`.
fn negate(_: &mut Ctx<'_>, args: &[Arg]) -> Outcome {
    let signature = || signature(true, "Neg", "IntValue", 1);
    let value = java_integer(arg(args, 0)?, signature)?;
    value.checked_neg().map(Value::Int).ok_or_else(|| overflow(format!("-{value}")))
}

#[cfg(test)]
mod tests {
    use tla_value::Value;

    use crate::Arg;
    use crate::stdlib::testing::{call, call_in, error, evaluator, int, string};

    fn apply(name: &str, left: i32, right: i32) -> Value {
        call("Naturals", name, &[int(left), int(right)]).unwrap()
    }

    fn apply_integers(name: &str, left: i32, right: i32) -> tla_value::Result<Value> {
        let args = vec![Arg::Value(int(left)), Arg::Value(int(right))];
        call_in(&evaluator(), "Naturals", name, true, args)
    }

    #[test]
    fn computes_like_tlc() {
        assert_eq!(apply("+", 2, 3).as_int(), Some(5));
        assert_eq!(apply("-", 2, 3).as_int(), Some(-1));
        assert_eq!(apply("*", -4, 3).as_int(), Some(-12));
        assert_eq!(apply("^", -2, 31).as_int(), Some(i32::MIN));
        assert_eq!(apply("^", -1, 7).as_int(), Some(-1));
        assert_eq!(apply("%", -7, 3).as_int(), Some(2));
        assert_eq!(apply("\\div", 7, 2).as_int(), Some(3));
        assert_eq!(apply("\\div", -7, 2).as_int(), Some(-4));
        assert_eq!(apply("..", 1, 3).to_string(), "1..3");
        assert_eq!(apply("<", 1, 2).as_bool(), Some(true));
        assert_eq!(apply("\\leq", 2, 2).as_bool(), Some(true));
        assert_eq!(apply("\\geq", 1, 2).as_bool(), Some(false));
        assert_eq!(call("Naturals", "Nat", &[]).unwrap().to_string(), "Nat");
        assert_eq!(call("Integers", "Int", &[]).unwrap().to_string(), "Int");
        assert_eq!(call("Integers", "-.", &[int(5)]).unwrap().as_int(), Some(-5));
    }

    #[test]
    fn rounds_division_as_each_java_class_does() {
        // Naturals floors only a quotient Java truncates below 0.
        assert_eq!(apply("\\div", -1, 2).as_int(), Some(0));
        assert_eq!(apply("\\div", 7, -2).as_int(), Some(-4));
        assert_eq!(apply("\\div", i32::MIN, -1).as_int(), Some(i32::MIN));
        assert_eq!(apply_integers("\\div", -1, 2).unwrap().as_int(), Some(-1));
        assert_eq!(apply_integers("\\div", 7, -2).unwrap().as_int(), Some(-4));
        assert_eq!(
            apply_integers("\\div", i32::MIN, -1).unwrap_err().0,
            "Overflow when computing -2147483648 \\div -1"
        );
    }

    #[test]
    fn fails_on_overflow() {
        let overflow =
            |name: &str, left: i32, right: i32| error("Naturals", name, &[int(left), int(right)]);
        assert_eq!(overflow("+", i32::MAX, 1), "Overflow when computing 2147483647+1");
        assert_eq!(overflow("-", i32::MIN, 1), "Overflow when computing -2147483648-1");
        assert_eq!(overflow("*", 65536, 65536), "Overflow when computing 65536*65536");
        assert_eq!(overflow("^", 2, 31), "Overflow when computing 2^31");
        assert_eq!(overflow("^", 3, 1000000), "Overflow when computing 3^1000000");
        assert_eq!(
            error("Integers", "-.", &[int(i32::MIN)]),
            "Overflow when computing --2147483648"
        );
    }

    #[test]
    fn fails_like_tlc_on_wrong_arguments() {
        assert_eq!(error("Naturals", "^", &[int(0), int(0)]), "0^0 is undefined.");
        assert_eq!(
            error("Naturals", "^", &[int(2), int(-1)]),
            "The second argument of ^ should be a natural number, but instead it is:\n-1"
        );
        assert_eq!(
            error("Naturals", "\\div", &[int(1), int(0)]),
            "The second argument of \\div is 0."
        );
        assert_eq!(
            error("Naturals", "%", &[int(1), int(0)]),
            "The second argument of % should be a positive number, but instead it is:\n0"
        );
        assert_eq!(
            error("Naturals", "+", &[int(1), string("a")]),
            "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntValue tlc2.module.Naturals.Plus(tlc2.value.impl.IntValue,tlc2.value.impl.IntValue),\nbut it produced the following error:\nCannot cast tlc2.value.impl.StringValue to tlc2.value.impl.IntValue"
        );
        assert_eq!(apply_integers("+", 1, 1).map(|value| value.as_int()).unwrap(), Some(2));
        let args = vec![Arg::Value(Value::TRUE), Arg::Value(int(1))];
        assert_eq!(
            call_in(&evaluator(), "Naturals", "..", true, args).unwrap_err().0,
            "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.IntervalValue tlc2.module.Integers.DotDot(tlc2.value.impl.IntValue,tlc2.value.impl.IntValue),\nbut it produced the following error:\nCannot cast tlc2.value.impl.BoolValue to tlc2.value.impl.IntValue"
        );
        assert_eq!(
            error("Naturals", "<", &[string("a"), int(1)]),
            "The first argument of < should be an integer, but instead it is:\n\"a\""
        );
        assert_eq!(
            error("Naturals", "\\geq", &[int(1), string("a")]),
            "The second argument of > should be an integer, but instead it is:\n\"a\""
        );
        let args = vec![Arg::Value(int(1)), Arg::Value(string("a"))];
        assert_eq!(
            call_in(&evaluator(), "Naturals", "\\geq", true, args).unwrap_err().0,
            "The second argument of >= should be an integer, but instead it is:\n\"a\""
        );
    }
}
