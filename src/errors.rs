use std::fmt;
use crate::span::{Position, Span, Spanned};
use crate::token::Token;
use crate::types::{Type, TypeVar};
use crate::symbol::{Symbol, SymbolArena};
use crate::hir;
use itertools::Itertools;

#[derive(Clone, Debug, PartialEq)]
pub enum ErrorKind {
    NameError(NameError),
    TypeError(TypeError),
    SyntaxError(SyntaxError),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Error {
    pub kind: ErrorKind,
    pub span: Span,
}

impl Error {
    pub fn underfined_var(symbol: Symbol, span: Span) -> Self {
        Error { kind: ErrorKind::NameError(NameError::UndefinedVariable { symbol }), span }
    }
    pub fn type_mismatch(expected: Type, found: Type, span: Span) -> Self {
        Error { kind: ErrorKind::TypeError(TypeError::MismatchedTypes { expected, found }), span }
    }
    pub fn occurs_check_error(var: TypeVar, ty: Type, span: Span) -> Self {
        Error { kind: ErrorKind::TypeError(TypeError::OccursCheckError { var, ty }), span }
    }
    pub fn invalid_bin_op(op: Spanned<hir::BinaryOperator>, left: Type, right: Type, span: Span) -> Self {
        Error { kind: ErrorKind::TypeError(TypeError::InvalidBinaryOperation { op, left, right }), span }
    }
    pub fn invalid_un_op(op: Spanned<hir::UnaryOperator>, operand: Type, span: Span) -> Self {
        Error { kind: ErrorKind::TypeError(TypeError::InvalidUnaryOperation { op, operand }), span }
    }
    pub fn assign_const_var(name: Spanned<Symbol>, span: Span) -> Self {
        Error { kind: ErrorKind::NameError(NameError::AssignConstVar { name }), span }
    }
    pub fn message(&self, symbol_arena: &SymbolArena) -> String {
        match &self.kind {
            ErrorKind::TypeError(type_error) => match type_error {
                TypeError::MismatchedTypes { expected, found } => 
                    format!("型の不一致: 期待される型 `{:?}` に対して `{:?}` が見つかりました", expected, found),
                TypeError::OccursCheckError { var, ty } => 
                    format!("再帰的な型定義: 型変数 `{:?}` が型 `{:?}` の中に現れています", var, ty),
                TypeError::InvalidBinaryOperation { op, left, right } => 
                    format!("無効な二項演算: 演算子 `{:?}` は型 `{:?}` と `{:?}` の間では使用できません", op.inner, left, right),
                TypeError::InvalidUnaryOperation { op, operand } => 
                    format!("無効な単項演算: 演算子 `{:?}` は型 `{:?}` に対して使用できません", op.inner, operand),
            },
            ErrorKind::NameError(name_error) => match name_error {
                NameError::UndefinedVariable { symbol } => 
                    format!("未定義の変数: {}", symbol_arena.get_name(symbol).unwrap()),
                NameError::AssignConstVar { name } => 
                    format!("定数への代入: {}", symbol_arena.get_name(&name.inner).unwrap()),
            },
            ErrorKind::SyntaxError(syntax_error) => {
                format!("構文エラー {} 予期されたトークン {} 実際のトークン {}",
                    syntax_error.message.iter().map(|s| format!("\"{}\"", s)).join(", "),
                    syntax_error.expected.iter().map(|s| format!("\"{}\"", s)).join(", "),
                    syntax_error.unexpected.iter().map(|s| format!("\"{}\"", s)).join(", "),
                )
            }
        }
    }
    pub fn location_string(&self) -> String {
        format!("{}行目 {}文字目", self.span.start.line, self.span.start.column)
    }
}
#[derive(Clone, Debug, PartialEq)]
pub enum NameError {
    UndefinedVariable {
        symbol: Symbol,
    },
    AssignConstVar {
        name: Spanned<Symbol>
    }
}
#[derive(Clone, Debug, PartialEq)]
pub enum TypeError {
    MismatchedTypes {
        expected: Type,
        found: Type,
    },
    InvalidBinaryOperation {
        op: Spanned<hir::BinaryOperator>,
        left: Type,
        right: Type,
    },
    InvalidUnaryOperation {
        op: Spanned<hir::UnaryOperator>,
        operand: Type,
    },
    OccursCheckError {
        var: TypeVar,
        ty: Type,
    },
}
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct SyntaxError {
    pub unexpected: Vec<String>,
    pub expected: Vec<String>,
    pub message: Vec<String>,
}

impl fmt::Display for NameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NameError::UndefinedVariable { symbol } => {
                write!(f, "未定義の変数: Symbol({})", symbol.get_id())
            }
            NameError::AssignConstVar { name } => {
                write!(f, "定数への代入: Symbol({})", name.inner.get_id())
            }
        }
    }
}