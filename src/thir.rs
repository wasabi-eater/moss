use std::rc::Rc;
use std::fmt;
use itertools::Itertools;

use crate::{span::{Span, Spanned}, hir::{BinaryOperator, UnaryOperator}, metadata::types::Type};
use crate::symbol::Symbol;

#[derive(PartialEq)]
pub(crate) struct Expression {
    pub(crate) kind: ExpressionKind,
    pub(crate) span: Span,
    pub(crate) type_: Type
}
#[derive(PartialEq)]
pub(crate) enum ExpressionKind {
    BinaryOp{
        left: Box<Expression>,
        op: Spanned<BinaryOperator>,
        right: Box<Expression>
    },
    PrefixUnaryOp{
        op: Spanned<UnaryOperator>,
        operand: Box<Expression>
    },
    Variable{
        name: Symbol
    },
    Assingment {
        var_name: Spanned<Symbol>,
        value: Box<Expression>
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
    Literal(Literal),
    If {
        cond: Box<Expression>,
        then: Box<Expression>,
        otherwise: Option<Box<Expression>>
    }
}
impl fmt::Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            ExpressionKind::BinaryOp { left, op, right } => write!(f, "({:?} {:?} {:?}: {:?})", left, op, right, self.type_),
            ExpressionKind::PrefixUnaryOp { op, operand } => write!(f, "({:?} {:?}: {:?})", op, operand, self.type_),
            ExpressionKind::Variable { name } => write!(f, "Symbol({}): {:?}", name.get_id(), self.type_),
            ExpressionKind::Assingment { var_name, value } => write!(f, "Symbol({}) = {:?}", var_name.inner.get_id(), value),
            ExpressionKind::Block { statements } => write!(f, "{{ {} }}", statements.iter().map(|s| format!("{:?}", s)).join("; ")),
            ExpressionKind::DeclareVar { is_const, name, value, scope } => write!(f, "{} Symbol({}) = {:?} in {:?}: {:?}", if *is_const { "let" } else { "var" }, name.inner.get_id(), value, scope, self.type_),
            ExpressionKind::Literal(literal) => write!(f, "{:?}", literal),
            ExpressionKind::If { cond, then, otherwise } => write!(f, "if {:?} then {:?} else {:?}", cond, then, otherwise),
        }
    }
}
#[derive(PartialEq)]
pub(crate) enum Literal {
    Int(Rc<str>),
    String(Rc<str>),
    Float(Rc<str>),
    Bool(bool)
}
impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Int(n) => write!(f, "{n}"),
            Literal::Bool(b) => write!(f, "{b}"),
            Literal::String(s) => write!(f, "{s}"),
            Literal::Float(n) => write!(f, "{n}")
        }
    }
}