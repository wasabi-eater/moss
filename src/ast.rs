use std::fmt;
use std::rc::Rc;
use crate::span::{Span, Spanned};
use itertools::Itertools;

pub(crate) fn connect_spans(from: Span, to: Span) -> Span {
    assert!(from.start <= to.start && from.end <= to.end, "Invalid span connection: {:?} -> {:?}", from, to);
    Span {
        start: from.start,
        end: to.end,
    }
}
#[derive(PartialEq)]
pub enum ExpressionKind {
    Variable(Rc<str>),
    Int(Rc<str>),
    Float(Rc<str>),
    StringLiteral(Rc<str>),
    Bool(bool),
    BinaryOperation(Box<Expression>, Spanned<String>, Box<Expression>),
    PrefixUnaryOperation(Spanned<String>, Box<Expression>),
    PostfixUnaryOperation(Box<Expression>, Spanned<String>),
    Block(Vec<Expression>),
    Assignment(Spanned<Rc<str>>, Box<Expression>),
    Let(Spanned<Rc<str>>, Box<Expression>),
    Var(Spanned<Rc<str>>, Box<Expression>)
}
pub type Expression = Spanned<ExpressionKind>;
impl ExpressionKind {
    pub(crate) fn variable(name: impl Into<Rc<str>>) -> Self {
        ExpressionKind::Variable(name.into())
    }
    pub(crate) fn int(value: impl Into<Rc<str>>) -> Self {
        ExpressionKind::Int(value.into())
    }
    pub(crate) fn float(value: impl Into<Rc<str>>) -> Self {
        ExpressionKind::Float(value.into())
    }
    pub(crate) fn boolean(value: bool) -> Self {
        ExpressionKind::Bool(value)
    }
    pub(crate) fn string_literal(value: impl Into<Rc<str>>) -> Self {
        ExpressionKind::StringLiteral(value.into())
    }
    pub(crate) fn binary_operation(left: Expression, op: Spanned<String>, right: Expression) -> Self {
        ExpressionKind::BinaryOperation(Box::new(left), op, Box::new(right))
    }
    pub(crate) fn prefix_unary_operation(op: Spanned<String>, expr: Expression) -> Self {
        ExpressionKind::PrefixUnaryOperation(op, Box::new(expr))
    }
    pub(crate) fn postfix_unary_operation(expr: Expression, op: Spanned<String>) -> Self {
        ExpressionKind::PostfixUnaryOperation(Box::new(expr), op)
    }
    pub(crate) fn block(statements: impl IntoIterator<Item = Expression>) -> Self {
        ExpressionKind::Block(statements.into_iter().collect())
    }
    pub(crate) fn assignment(name: Spanned<Rc<str>>, expr: Expression) -> Self {
        ExpressionKind::Assignment(name, Box::new(expr))
    }
    pub(crate) fn let_(name: Spanned<Rc<str>>, expr: Expression) -> Self {
        ExpressionKind::Let(name, Box::new(expr))
    }
    pub(crate) fn var(name: Spanned<Rc<str>>, expr: Expression) -> Self {
        ExpressionKind::Var(name, Box::new(expr))
    }
}

impl fmt::Debug for ExpressionKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExpressionKind::Variable(name) => write!(f, "{}", name),
            ExpressionKind::Int(value) => write!(f, "{}", value),
            ExpressionKind::Float(value) => write!(f, "{}", value),
            ExpressionKind::Bool(value) => write!(f, "{}", value),
            ExpressionKind::StringLiteral(value) => write!(f, "{}", value),
            ExpressionKind::BinaryOperation(left, op, right) => write!(f, "({:?} {:?} {:?})", left, op, right),
            ExpressionKind::PrefixUnaryOperation(op, expr) => write!(f, "({:?} {:?})", op, expr),
            ExpressionKind::PostfixUnaryOperation(expr, op) => write!(f, "({:?} {:?})", expr, op),
            ExpressionKind::Block(statements) => write!(f, "{{ {} }}", statements.iter().map(|s| format!("{:?}", s)).join("; ")),
            ExpressionKind::Assignment(name, expr) => write!(f, "{:?} = {:?}", name, expr),
            ExpressionKind::Let(name, expr) => write!(f, "let {:?} = {:?}", name, expr),
            ExpressionKind::Var(name, expr) => write!(f, "var {:?} = {:?}", name, expr),
        }
    }
}