//! Subexpression references: positional selectors, labels, `LET` definitions, binders, and
//! instances. The cases and values come from TLC's test206, test209, and test216, and tla-ts's
//! `Subexpressions` fixture, which TLC checks.

mod common;

use common::{eval, evaluator_with, show};

/// Each named definition must equal `TRUE`.
fn assert_true(body: &str, modules: &[(&str, &str)], names: &[&str]) {
    let evaluator = evaluator_with(body, modules, Vec::new());
    for name in names {
        match eval(&evaluator, name) {
            Ok(value) => assert_eq!(value.to_string(), "TRUE", "{name}"),
            Err(error) => panic!("{name}: {error}"),
        }
    }
}

#[test]
fn selects_operands_by_position() {
    let body = r#"
EXTENDS Naturals, Sequences
xx == <<11, <<22,33>>, 33>>
F(a) == /\ TRUE
        /\ TRUE
        /\ Len(xx[a]) > 0
        /\ TRUE
A1 == F(2)!3 = (Len(xx[2]) > 0)
A2 == F(2)!3!1!1!2 = 2
A3 == F(2)!3!<<!<<!<< = xx
G == [xx EXCEPT ![1] = 42, ![2] = 55]
H == xx.foo
I == [fld1 |-> 1, fld2 |->2, fld3 |-> 3]
J == [fld1 : 1, fld2 :2, fld3 : 3]
A4 == G!1 = xx /\ H!1 = xx /\ H!2 = "foo" /\ I!3 = 3 /\ J!3 = 3
K == IF 41 THEN 42 ELSE 43
L == CASE 1 -> 11 [] 2 -> 22 [] OTHER -> 33
A5 == K!1 = 41 /\ K!3 = 43 /\ L!1!1 = 1 /\ L!2!2 = 22 /\ L!3!2 = 33
M == LET Z == 23 IN Z
Z == 44
A6 == M!1 = 23
NN == 55
N == [44]_NN
P == WF_NN(44)
A7 == N!1 = 44 /\ N!2 = 55 /\ P!1 = 55 /\ P!2 = 44
R == \E x \in {1}, y \in {2} : x + y  > 2
S == [x, y \in {1, 2}, z \in {3} |-> x+y+z]
A8 == R!1 = {1} /\ R!2 = {2} /\ R!(1,2)!<< = 3 /\ S!1 = {1, 2} /\ S!(2, 3, 4) = 9
Def5 == [i \in 1..10 |-> i+1][3]
Def11 == {1} \X {2} \X {3}
Def13 == \A x : CASE x=1 -> 1 [] x=2 -> 2 [] OTHER -> 3
A9 == Def5!>> = 3 /\ Def5!<<[4] = 5 /\ Def11!3!1 = 3 /\ Def13!(42)!1!<<!<< = 42
"#;
    let names = ["A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8", "A9"];
    assert_true(body, &[], &names);
}

#[test]
fn selects_labels_and_let_definitions() {
    let body = r#"
EXTENDS Integers
C == 4
Op(Arg(_), p) ==
   \A x \in {1,2}, <<y, z>> \in {<<3, 4>>} :
       lab(x,y,z) :: LET a ++ b == Arg(a) + b + x + 2*y + 3*z
                     IN (Arg(1) + Arg(p) + C + 2*x + 4*y + 6*z) = 1 ++ (label2 :: p ++ C)
Foo(u) == 2*u
A1 == Op(Foo, 9)!lab(1,2,3)!label2 = Op(Foo, 9)!lab(1,2,3)!:!++(9, 4)
Op1(a) == \A x \in {} : lab(x) :: IF TRUE
                                 THEN LET Op1a(c) == 4 * c + a*x
                                      IN  a + Op1a(x)
                                 ELSE 1
A2 == Op1(2)!(3)!2!1 = 2 + 4*3 + 6 /\ Op1(2)!(3)!2!Op1a(4) = 16 + 6
COp(q, p) == CHOOSE x : lab(x) :: LET a ++ b == {a, b, q, p, x} IN <<q, 99 ++ p>>
A3 == COp(1, 2)!(3)!++(4, 5) = {2,1, 3, 4, 5} /\ COp(1, 2)!lab(3)!:!++(4, 5) = {2,1, 3, 4, 5}
A4 == COp(1, 2)!(3)!1!>> = {99, 1, 2, 3}
COp2(q, p) == CHOOSE x : lab(x) :: LET a ++ b == {lab(y):: y + a + b : y \in {1}}
                                   IN <<q, 99 ++ p >>
A5 == COp2(1,2)!lab(3)!:!++(9,10)!lab(11) = 30 /\ COp2(1,2)!(3)!++(9,10)!(11) = 30
THEOREM Thm2 == lab3 :: TRUE
A6 == Thm2!lab3
"#;
    assert_true(body, &[], &["A1", "A2", "A3", "A4", "A5", "A6"]);
}

#[test]
fn passes_selections_as_operator_arguments() {
    let body = r#"
EXTENDS Integers
OOp2(A(_,_), a, b) == A(a, b)
OOp3(A(_,_,_), a, b, c) == A(a, b, c)
OOp6(A(_, _, _, _, _, _), a1, a2, a3, a4, a5, a6) == A(a1, a2, a3, a4, a5, a6)
SOp1a(a) == {x \in {1,2} : a = x}
SOp1b(a) == {x + a : x \in {1,2}}
SOp1d(a) == {(LET c(y) == (a * x) + y IN x + a)  : x \in {1,2}}
Op1(a) == \A x \in {} : lab(x) :: IF TRUE THEN LET Op1a(c) == 4 * c + a*x IN a + Op1a(x) ELSE 1
COp2(q, p) == CHOOSE x : lab(x) :: LET a ++ b == {lab(y):: y + a + b : y \in {1}}
                                   IN <<q, 99 ++ p >>
A1 == OOp2(SOp1a!@, 2, 2) = TRUE /\ OOp2(SOp1b!@, 2, 3) = 5
A2 == OOp3(SOp1d!@!c, 2, 3, 4) = 2 * 3 + 4 /\ OOp3(Op1!@!2!Op1a, 2, 3, 4) = 22
A3 == OOp6(COp2!lab!:!++!lab, 1, 2, 3, 9, 10, 11) = 30
A4 == OOp6(COp2!@!++!lab, 1, 2, 3, 9, 10, 11) = 30
"#;
    assert_true(body, &[], &["A1", "A2", "A3", "A4"]);
}

const ARITHMETIC: &str = r#"
---- MODULE Arithmetic ----
EXTENDS Naturals
CONSTANT Offset
Double(n) == sum :: n + n + Offset
Ranges(n) == {k \in 0..n : even(k) :: k % 2 = 0}
THEOREM Thm == Offset + 0 = 1
====
"#;

const BARS: &str = r#"
---- MODULE Bars ----
CONSTANT A5(_, _, _, _, _)
Bar(a) == <<1, a>>
Bar4(a) == {x \in {1} : lab(x) :: <<x, a>>}
Bar5(a) == {x \in {1} : lab(x) :: LET b ++ c == <<a, b, c, x>> IN 42}
====
"#;

#[test]
fn selects_through_instances() {
    let body = r#"
EXTENDS Naturals
A == INSTANCE Arithmetic WITH Offset <- 1
P(k) == INSTANCE Arithmetic WITH Offset <- k
INSTANCE Arithmetic WITH Offset <- 1
A1 == A!Double(4)!sum = 9 /\ A!Double(4)!1 = 8 /\ A!Double(4)!1!<< = 4
A2 == A!Ranges(4)!even(3) = FALSE /\ A!Thm!: /\ Thm!<< = 1
A3 == P(5)!Double(4)!sum = 13 /\ P(5)!Thm!1 = 5
OOp2(Op(_,_), a, b) == Op(a, b)
Five(a, b, c, d, e) == a + b + c + d + e
Inst == INSTANCE Bars WITH A5 <- Five
A4 == Inst!Bar(3)!>> = 3 /\ Inst!Bar4(1)!(2)!<< = 2 /\ Inst!Bar4(1)!lab(2)!>> = 1
A5 == OOp2(Inst!Bar4!@!<<, 1, 2) = 2 /\ OOp2(Inst!Bar4!lab!>>, 1, 2) = 1
A6 == Inst!Bar5(1)!lab(2)!:!++(3, 4) = <<1, 3, 4, 2>>
"#;
    let modules = [("Arithmetic", ARITHMETIC), ("Bars", BARS)];
    assert_true(body, &modules, &["A1", "A2", "A3", "A4", "A5", "A6"]);
}

#[test]
fn shows_selected_values() {
    let printed = show(
        "EXTENDS Naturals\nPair(a, b) == {y \\in a..b : keep(y) :: y % 2 = 0}\nRange == Pair(1, 4)!1\nKeep == Pair(1, 4)!keep(3)",
        &["Range", "Keep"],
    );
    assert_eq!(printed, ["1..4", "FALSE"]);
}

const PARTS: &str = r#"
---- MODULE Parts ----
CONSTANT A5(_, _, _, _, _)
Foo(a1, a2, a3, a4, a5) == A5(a1, a2, a3, a4, a5)
Bar5(a) == {x \in {1} : lab(x) :: LET b ++ c == <<a, b, c, x>> IN 42}
====
"#;

#[test]
fn passes_an_operator_symbol_ending_a_reference_as_an_operator() {
    // The grammar reads `COp!@!++` only after the parser masks the `++` (TLC's test206).
    let body = r#"
COp(q, p) == CHOOSE x : lab(x) :: LET a ++ b == {a, b, q, p, x} IN <<q, 99 ++ p>>
OOp4(A(_,_,_,_), a, b, c, d) == A(a, b, c, d)
OOp5(A(_, _, _, _, _), a1, a2, a3, a4, a5) == A(a1, a2, a3, a4, a5)
Inst == INSTANCE Parts WITH A5 <- COp!@!++
Inst2(A5(_, _, _, _, _)) == INSTANCE Parts
A1 == OOp5(COp!@!++, 1, 2, 3, 4, 5) = {2,1, 3, 4, 5}
A2 == Inst!Foo(1, 2, 3, 4, 5) = {2,1, 3, 4, 5}
A3 == OOp4(Inst!Bar5!lab!:!++, 1, 2, 3, 4) = <<1, 3, 4, 2>>
A4 == Inst2(COp!@!++)!Foo(1, 2, 3, 4, 5) = {2,1, 3, 4, 5}
"#;
    assert_true(body, &[("Parts", PARTS)], &["A1", "A2", "A3", "A4"]);
}
