//! SANY's `Operators` and `OperatorStack`, with which `TLAplusParser` orders the operators of
//! an expression by precedence as it parses, and rejects orders precedence can't settle.

use std::collections::HashMap;
use std::rc::Rc;
use std::sync::LazyLock;

use super::grammar::{Unit, action};
use super::{Node, State};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Fix {
    Prefix,
    Postfix,
    Infix,
    Nfix,
}

/// An `Operator` of `Operators.CanonicalOperators`. None of them is right-associative.
#[derive(Debug)]
pub(super) struct Operator {
    pub(super) name: &'static str,
    low: u8,
    high: u8,
    is_left_associative: bool,
    pub(super) fix: Fix,
}

impl PartialEq for Operator {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

/// An `OSelement` of `OperatorStack`: an operand, or an operator with its node.
#[derive(Clone)]
pub(super) struct StackElement {
    pub(super) node: Rc<Node>,
    pub(super) operator: Option<&'static Operator>,
}

type Group = (Fix, u8, u8, bool, &'static [&'static str]);

/// `Operators.CanonicalOperators`, but for `.`, which only `OperatorStack.reduceRecord`
/// handles.
const CANONICAL_OPERATORS: &[Group] = &[
    (Fix::Postfix, 160, 160, true, &["["]),
    (Fix::Postfix, 150, 150, false, &["'", "^+", "^*", "^#"]),
    (Fix::Prefix, 120, 120, false, &["-."]),
    (Fix::Prefix, 100, 130, false, &["SUBSET", "UNION", "DOMAIN"]),
    (Fix::Prefix, 40, 150, false, &["[]", "<>", "ENABLED", "UNCHANGED"]),
    (Fix::Prefix, 40, 40, true, &["\\lnot"]),
    (Fix::Nfix, 100, 130, true, &["\\times"]),
    (Fix::Infix, 140, 140, false, &["^", "^^"]),
    (Fix::Infix, 130, 130, false, &["/", "//", "\\oslash", "\\div"]),
    (
        Fix::Infix,
        130,
        130,
        true,
        &["*", "&&", "&", "**", "\\odot", "\\otimes", "\\star", "\\o", "\\bigcirc", "\\bullet"],
    ),
    (Fix::Infix, 110, 110, true, &["-", "--", "\\ominus"]),
    (Fix::Infix, 100, 110, true, &["|", "||", "%%"]),
    (Fix::Infix, 100, 110, false, &["%"]),
    (Fix::Infix, 100, 100, true, &["+", "++", "\\oplus"]),
    (Fix::Infix, 90, 140, false, &["\\wr"]),
    (Fix::Infix, 90, 130, true, &["$$", "$", "??", "##", "\\uplus", "\\sqcap", "\\sqcup"]),
    (Fix::Infix, 90, 130, false, &["!!"]),
    (Fix::Infix, 90, 90, false, &["...", ".."]),
    (Fix::Infix, 80, 80, true, &["\\intersect", "\\union"]),
    (Fix::Infix, 80, 80, false, &["\\"]),
    (Fix::Infix, 70, 70, false, &["<:", ":>"]),
    (Fix::Infix, 60, 60, true, &["@@"]),
    (Fix::Infix, 50, 140, true, &["\\cdot"]),
    (
        Fix::Infix,
        50,
        50,
        false,
        &[
            "=",
            "/=",
            "<",
            ">",
            "\\in",
            "\\notin",
            "\\leq",
            "\\geq",
            "\\subseteq",
            "\\subset",
            "\\supseteq",
            "\\supset",
            "\\sqsubseteq",
            "\\sqsubset",
            "\\sqsupseteq",
            "\\sqsupset",
            "\\prec",
            "\\preceq",
            "\\succ",
            "\\succeq",
            "\\sim",
            "\\simeq",
            "\\approx",
            "\\cong",
            "\\asymp",
            "\\doteq",
            "\\propto",
            "\\ll",
            "\\gg",
            "|-",
            "|=",
            "-|",
            "=|",
            ":=",
            "::=",
        ],
    ),
    (Fix::Infix, 30, 30, true, &["\\land", "\\lor"]),
    (Fix::Infix, 20, 20, false, &["~>", "\\equiv", "-+->"]),
    (Fix::Infix, 10, 10, false, &["=>"]),
];

/// The spellings of each operator, the one SANY names it by first: `Operators`' synonyms.
/// tla-tools-resolve keeps the same list for SANY's names of the operators.
const OPERATOR_SYNONYMS: &[&[&str]] = &[
    &["\\lnot", "~", "\\neg", "¬"],
    &["[]", "□"],
    &["<>", "◇"],
    &["\\land", "/\\", "∧"],
    &["\\lor", "\\/", "∨"],
    &["\\equiv", "<=>", "≡", "⇔"],
    &["/=", "#", "≠"],
    &["\\leq", "<=", "=<", "≤"],
    &["\\geq", ">=", "≥"],
    &["\\times", "\\X", "×"],
    &["\\intersect", "\\cap", "∩"],
    &["\\union", "\\cup", "∪"],
    &["\\o", "\\circ", "∘"],
    &["\\oplus", "(+)", "⊕"],
    &["\\ominus", "(-)", "⊖"],
    &["\\odot", "(.)", "⊙"],
    &["\\oslash", "(/)", "⊘"],
    &["\\otimes", "(\\X)", "⊗"],
    &["\\approx", "≈"],
    &[":=", "≔"],
    &["\\asymp", "≍"],
    &["\\bigcirc", "◯"],
    &["::=", "⩴"],
    &["\\bullet", "●"],
    &["\\cdot", "⋅"],
    &["\\cong", "≅"],
    &["\\div", "÷"],
    &["\\doteq", "≐"],
    &["..", "‥"],
    &["...", "…"],
    &["!!", "‼"],
    &["\\gg", "≫"],
    &["=>", "⇒"],
    &["\\in", "∈"],
    &["=|", "⫤"],
    &["~>", "↝"],
    &["\\ll", "≪"],
    &["-|", "⊣"],
    &["\\notin", "∉"],
    &["-+->", "⇸"],
    &["\\prec", "≺"],
    &["\\preceq", "⪯"],
    &["\\propto", "∝"],
    &["??", "⁇"],
    &["|=", "⊨"],
    &["|-", "⊢"],
    &["\\sim", "∼"],
    &["\\simeq", "≃"],
    &["\\sqcap", "⊓"],
    &["\\sqcup", "⊔"],
    &["\\sqsubset", "⊏"],
    &["\\sqsubseteq", "⊑"],
    &["\\sqsupset", "⊐"],
    &["\\sqsupseteq", "⊒"],
    &["\\star", "⋆"],
    &["\\subset", "⊂"],
    &["\\subseteq", "⊆"],
    &["\\succ", "≻"],
    &["\\succeq", "⪰"],
    &["\\supset", "⊃"],
    &["\\supseteq", "⊇"],
    &["\\uplus", "⊎"],
    &["||", "‖"],
    &["\\wr", "≀"],
    &["^+", "⁺"],
];

/// `Operator.VoidOperator`, which `OperatorStack.finalReduce` pushes to reduce the whole stack.
pub(super) static VOID_OPERATOR: Operator =
    Operator { name: "$$_void", low: 0, high: 0, is_left_associative: false, fix: Fix::Infix };

static OPERATORS: LazyLock<HashMap<&'static str, &'static Operator>> = LazyLock::new(|| {
    let mut operators = HashMap::new();
    for (fix, low, high, is_left_associative, names) in CANONICAL_OPERATORS {
        for name in *names {
            let operator = Operator {
                name,
                low: *low,
                high: *high,
                is_left_associative: *is_left_associative,
                fix: *fix,
            };
            operators.insert(*name, &*Box::leak(Box::new(operator)));
        }
    }
    for synonyms in OPERATOR_SYNONYMS {
        if let Some(canonical) = operators.get(synonyms[0]).copied() {
            for synonym in &synonyms[1..] {
                operators.insert(*synonym, canonical);
            }
        }
    }
    operators
});

/// `Operators.getOperator`, which knows an operator by its name or a synonym.
pub(super) fn operator(name: &str) -> Option<&'static Operator> {
    OPERATORS.get(name).copied()
}

/// `OperatorStack`'s `fcnOp`, which a function application's `[` pushes.
pub(super) fn function_operator() -> &'static Operator {
    operator("[").expect("[ is an operator")
}

/// `Operator.succ` and `Operator.prec`: whether `left` binds tighter than `right`, or looser.
fn is_tighter(left: &Operator, right: &Operator) -> bool {
    left.low > right.high
}

pub(super) fn is_looser(left: &Operator, right: &Operator) -> bool {
    left.high < right.low
}

/// `Operators.getMixfix`, which turns `-` into the prefix `-.`.
fn mixfix(operator: &'static Operator) -> Option<&'static Operator> {
    match operator.fix {
        Fix::Prefix => Some(operator),
        _ => self::operator(&format!("{}.", operator.name)),
    }
}

/// `OperatorStack.reducePostfix`: replaces the operand and postfix operator below index `top`
/// with their expression.
pub(super) fn reduce_postfix(stack: &mut Vec<StackElement>, top: usize) {
    let operand = stack[top - 2].node.clone();
    let postfix = stack[top - 1].clone();
    let node = match postfix.operator == Some(function_operator()) {
        true => {
            let mut heirs = vec![operand];
            heirs.extend(postfix.node.heirs.iter().cloned());
            Node::new("FcnAppl", heirs)
        }
        false => Node::new("PostfixExpr", vec![operand, postfix.node]),
    };
    stack.splice(top - 2..top, [StackElement { node, operator: None }]);
}

/// `OperatorStack.reducePrefix` and `reduceInfix`: replace the operator below the top of the
/// stack and its operands with their expression.
fn reduce_operator(stack: &mut Vec<StackElement>, operator: &Operator) {
    let top = stack.len() - 1;
    if !matches!(operator.fix, Fix::Infix | Fix::Nfix) {
        let node =
            Node::new("PrefixExpr", vec![stack[top - 2].node.clone(), stack[top - 1].node.clone()]);
        stack.splice(top - 2..top, [StackElement { node, operator: None }]);
        return;
    }
    let left = stack[top - 3].node.clone();
    let is_times = operator.fix == Fix::Nfix;
    let mut heirs = match is_times && left.kind == "Times" {
        true => left.heirs.clone(),
        false => vec![left],
    };
    heirs.extend([stack[top - 2].node.clone(), stack[top - 1].node.clone()]);
    let node = Node::new(if is_times { "Times" } else { "InfixExpr" }, heirs);
    stack.splice(top - 3..top, [StackElement { node, operator: None }]);
}

/// `OperatorStack.reduceStack`, run when an operator is pushed: it reduces the operators below
/// it that bind tighter, and gives the message it throws where precedence can't order two
/// operators, or two operands follow each other. The grammar pushes an infix or postfix
/// operator only after an operand, except for a `-` that Expression takes for a prefix one, so
/// the checks that reject other orders never fail and are left out.
pub(super) fn reduce_stack(state: &mut State) -> Option<String> {
    let stack = state.operator_stack();
    let top = stack.len().checked_sub(1)?;
    let right = stack[top].clone();
    let right_operator = right.operator.filter(|operator| operator.fix != Fix::Prefix)?;
    let middle = stack[top.checked_sub(1)?].clone();
    let left = top.checked_sub(2).map(|index| stack[index].clone());
    if middle.operator.is_some_and(|operator| operator.fix == Fix::Postfix) {
        reduce_postfix(stack, top);
        return reduce_stack(state);
    }
    if let Some(middle_operator) = middle.operator {
        let mixfix = mixfix(right_operator)?;
        return is_tighter(middle_operator, mixfix).then(|| {
            format!(
                "\n  Precedence conflict between ops {} in block {} and {}.",
                middle_operator.name,
                state.node_location(&middle.node),
                mixfix.name
            )
        });
    }
    let left = left?;
    let Some(left_operator) = left.operator else {
        return Some(format!(
            "Expression at location {} and expression at location {} follow each other without any intervening operator.",
            state.node_location(&left.node),
            state.node_location(&middle.node)
        ));
    };
    if right_operator.fix == Fix::Postfix {
        if is_looser(left_operator, right_operator) {
            return None;
        }
        if !is_tighter(left_operator, right_operator) {
            return Some(format!(
                "Precedence conflict between ops {} in block {} and {}.",
                left_operator.name,
                state.node_location(&right.node),
                right_operator.name
            ));
        }
        reduce_operator(state.operator_stack(), left_operator);
        return reduce_stack(state);
    }
    let stack = state.operator_stack();
    let operator = match mixfix(left_operator) {
        Some(mixfix) if top == 2 || stack[top - 3].operator.is_some() => mixfix,
        _ => left_operator,
    };
    if is_looser(operator, right_operator) {
        return None;
    }
    if !is_tighter(operator, right_operator)
        && !(operator == right_operator && operator.is_left_associative)
    {
        return Some(format!(
            "\n  Precedence conflict between ops {} in block {} and {}.",
            operator.name,
            state.node_location(&left.node),
            right_operator.name
        ));
    }
    if operator.fix != Fix::Postfix {
        reduce_operator(stack, operator);
        return reduce_stack(state);
    }
    let location = state.node_location(&left.node);
    let is_on_earlier_line =
        state.token(left.node.first).line < state.token(middle.node.first).line;
    if is_on_earlier_line && right_operator.name == "=" {
        return Some(format!(
            "\n  *** Hint *** You may have mistyped ==\n  Illegal combination of operators {} in block {location} and =.",
            operator.name
        ));
    }
    Some(match *right_operator == VOID_OPERATOR {
        true => {
            format!("\n Error following expression at  {location}, missing operator or separator.")
        }
        false => format!(
            "\n  Illegal combination of operators {} in block {location} and {}.",
            operator.name, right_operator.name
        ),
    })
}

/// `OperatorStack.pushOnStack` for the node of the production just parsed: an operand, or, if
/// `is_operator` holds of it, an operator, which `reduce_stack` reduces with what is below it.
pub(super) fn push_on_stack(is_operator: fn(&Node) -> bool) -> Unit {
    action(move |state| {
        let node = state.heir(1);
        let operator = is_operator(&node).then_some(state.last_operator).flatten();
        let is_operand = !is_operator(&node);
        let stack = state.operator_stack();
        stack.push(StackElement { node, operator });
        match is_operand || stack.len() == 1 {
            true => None,
            false => reduce_stack(state),
        }
    })
}

pub(super) fn push_operand() -> Unit {
    push_on_stack(|_| false)
}

pub(super) fn push_operator() -> Unit {
    push_on_stack(|_| true)
}

/// `TLAplusParser`'s `lastOp`, which the productions of operators set.
pub(super) fn set_last_operator() -> Unit {
    action(|state| {
        state.last_operator = operator(&state.token(state.token).image);
        None
    })
}
