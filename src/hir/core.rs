use std::rc::Rc;
use std::fmt;
use crate::span::{Span, Spanned};
use crate::symbol::Symbol;
use itertools::Itertools;

/// HIRの式を表現する構造体
#[derive(Clone, PartialEq)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub span: Span
}

/// HIRの式の種類を表現する列挙型
#[derive(Clone, PartialEq)]
pub enum ExpressionKind {
    Variable {
        name: Symbol,
    },
    Literal(Literal),
    BinaryOp {
        op: Spanned<BinaryOperator>,
        left: Box<Expression>,
        right: Box<Expression>,
    },
    PrefixUnaryOp {
        op: Spanned<UnaryOperator>,
        operand: Box<Expression>,
    },
    Assignment {
        name: Spanned<Symbol>,
        value: Box<Expression>,
    },
    Block {
        statements: Vec<Expression>
    },
    DeclareVar {
        is_const: bool,
        name: Spanned<Symbol>,
        value: Box<Expression>,
        scope: Box<Expression>
    },
    If {
        cond: Box<Expression>,
        then: Box<Expression>,
        otherwise: Option<Box<Expression>>
    }
}
impl fmt::Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}
impl fmt::Debug for ExpressionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExpressionKind::Variable { name} => write!(f, "{:?}", name),
            ExpressionKind::Literal(literal) => write!(f, "{:?}", literal),
            ExpressionKind::BinaryOp { op, left, right } => write!(f, "({:?} {:?} {:?})", left, op, right),
            ExpressionKind::PrefixUnaryOp { op, operand } => write!(f, "({:?} {:?})", op, operand),
            ExpressionKind::Assignment { name, value } => write!(f, "{:?} = {:?}", name, value),
            ExpressionKind::Block { statements } => write!(f, "{{ {} }}", statements.iter().map(|s| format!("{:?}", s)).join("; ")),
            ExpressionKind::DeclareVar { is_const, name, value, scope } => write!(f, "{} {:?} = {:?} in {:?}", if *is_const { "let" } else { "var" }, name, value, scope),
            ExpressionKind::If { cond, then, otherwise } => write!(f, "if {:?} then {:?} else {:?}", cond, then, otherwise),
        }
    }
}

/// リテラル値を表現する列挙型
#[derive(Clone, PartialEq)]
pub enum Literal {
    Int(Rc<str>),
    Float(Rc<str>),
    String(Rc<str>),
    Bool(bool),
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            &Literal::Int(n) => write!(f, "{n}"),
            &Literal::Bool(b) => write!(f, "{b}"),
            &Literal::String(s) => write!(f, "{s}"),
            &Literal::Float(n) => write!(f, "{n}")
        }
    }
}

/// 二項演算子を表現する列挙型
#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    And,
    Or,
    Equal,
    NotEqual,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    Xor,
}
impl fmt::Debug for BinaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Subtract => write!(f, "-"),
            BinaryOperator::Multiply => write!(f, "*"),
            BinaryOperator::Divide => write!(f, "/"),
            BinaryOperator::And => write!(f, "&"),
            BinaryOperator::Or => write!(f, "|"),
            BinaryOperator::Equal => write!(f, "=="),
            BinaryOperator::NotEqual => write!(f, "!="),
            BinaryOperator::LessThan => write!(f, "<"),
            BinaryOperator::GreaterThan => write!(f, ">"),
            BinaryOperator::LessThanOrEqual => write!(f, "<="),
            BinaryOperator::GreaterThanOrEqual => write!(f, ">="),
            BinaryOperator::Xor => write!(f, "^"),
        }
    }
}
/// 単項演算子を表現する列挙型
#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub enum UnaryOperator {
    Minus,
    Not
}
impl fmt::Debug for UnaryOperator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnaryOperator::Minus => write!(f, "-"),
            UnaryOperator::Not => write!(f, "!"),
        }
    }
}