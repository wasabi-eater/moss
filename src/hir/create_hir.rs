use crate::ast::{self, Expression as AstExpression, ExpressionKind as AstExpressionKind};
use crate::errors::Error;
use crate::symbol::SymbolArena;
use super::core::*;
use std::rc::Rc;
use crate::span::{Span, Spanned};
/// ASTからHIRへの変換を行うための構造体
pub(crate) struct Maker {
    pub(crate) symbol_arena: SymbolArena,
}

impl Maker {
    pub fn new() -> Self {
        Maker {
            symbol_arena: SymbolArena::new()
        }
    }

    pub fn variable(&mut self, name: Rc<str>, span: Span) -> Result<Expression, Error> {
        let name = self.symbol_arena.symbol(name);
        Ok(Expression {
            kind: ExpressionKind::Variable { name },
            span,
        })
    }

    pub fn int_literal(&mut self, value: impl Into<Rc<str>>, span: Span) -> Result<Expression, Error> {
        Ok(Expression {
            kind: ExpressionKind::Literal(Literal::Int(value.into())),
            span
        })
    }

    pub fn float_literal(&mut self, value: impl Into<Rc<str>>, span: Span) -> Result<Expression, Error> {
        Ok(Expression {
            kind: ExpressionKind::Literal(Literal::Float(value.into())),
            span
        })
    }

    pub fn string_literal(&mut self, value: Rc<str>, span: Span) -> Result<Expression, Error> {
        Ok(Expression {
            kind: ExpressionKind::Literal(Literal::String(value)),
            span
        })
    }

    pub fn bool_literal(&mut self, value: bool, span: Span) -> Result<Expression, Error> {
        Ok(Expression {
            kind: ExpressionKind::Literal(Literal::Bool(value)),
            span
        })
    }

    pub fn binary_op(&mut self, op: Spanned<BinaryOperator>, left: Expression, right: Expression, span: Span) -> Result<Expression, Error> {
        Ok(Expression {
            kind: ExpressionKind::BinaryOp { op, left: Box::new(left), right: Box::new(right) },
            span
        })
    }

    pub fn prefix_unary_op(&mut self, op: Spanned<UnaryOperator>, operand: Expression, span: Span) -> Result<Expression, Error> {
        Ok(Expression {
            kind: ExpressionKind::PrefixUnaryOp { op, operand: Box::new(operand) },
            span
        })
    }

    pub fn assignment(&mut self, name: Spanned<Rc<str>>, value: Expression, span: Span) -> Result<Expression, Error> {
        let name = name.map(|name| self.symbol_arena.symbol(name));
        Ok(Expression {
            kind: ExpressionKind::Assignment { name, value: Box::new(value) },
            span
        })
    }

    pub fn block(&mut self, statements: impl IntoIterator<Item = Expression>, span: Span) -> Result<Expression, Error> {
        Ok(Expression {
            kind: ExpressionKind::Block { statements: statements.into_iter().collect() },
            span
        })
    }

    pub fn declare_var(&mut self, name: Spanned<Rc<str>>, value: Expression, span: Span, is_const: bool, scope: Expression) -> Result<Expression, Error> {
        let name = name.map(|name| self.symbol_arena.symbol(name));
        Ok(Expression {
            kind: ExpressionKind::DeclareVar {
                name,
                value: Box::new(value),
                is_const,
                scope: Box::new(scope)
            },
            span
        })
    }
    pub(crate) fn from_ast_expr(&mut self, ast: &AstExpression) -> Result<Expression, Error> {
        match &ast.inner {
            AstExpressionKind::BinaryOperation(left, op, right) => {
                let op = op.as_ref().map(|op| match op.as_str() {
                    "+" => BinaryOperator::Add,
                    "-" => BinaryOperator::Subtract,
                    "*" => BinaryOperator::Multiply,
                    "/" => BinaryOperator::Divide,
                    "==" => BinaryOperator::Equal,
                    "!=" => BinaryOperator::NotEqual,
                    ">" => BinaryOperator::GreaterThan,
                    ">=" => BinaryOperator::GreaterThanOrEqual,
                    "<" => BinaryOperator::LessThan,
                    "<=" => BinaryOperator::LessThanOrEqual,
                    "&" => BinaryOperator::And,
                    "|" => BinaryOperator::Or,
                    "^" => BinaryOperator::Xor,
                    _ => todo!("Unsupported binary operator: {}", op)
                });
                let left = self.from_ast_expr(left)?;
                let right = self.from_ast_expr(right)?; 
                Ok(Expression { 
                    kind: ExpressionKind::BinaryOp { op, left: Box::new(left), right: Box::new(right) },
                    span: ast.span,
                })
            },
            AstExpressionKind::Block(statements) => {
                let declarings = statements.iter().enumerate()
                    .filter_map(|(i, s)| match &s.inner {
                        AstExpressionKind::Let(name, expr) => Some((i, name.clone(), expr, true, s.span)),
                        AstExpressionKind::Var(name, expr) => Some((i, name.clone(), expr, false, s.span)),
                        _ => None
                    });
                let mut result = None;
                let mut last_pos = statements.len();
                for (pos, name, value, is_const, declare_span) in declarings.into_iter().rev() {
                    let mut statements: Vec<Expression> = statements[pos + 1..last_pos].iter()
                        .map(|statement| self.from_ast_expr(statement))
                        .collect::<Result<_, _>>()?;
                    statements.extend(result);
                    let statements_span = if statements.is_empty() {
                        Span { start: declare_span.end, end: declare_span.end }
                    } else {
                        ast::connect_spans(statements[0].span, statements.last().unwrap().span)
                    };
                    let block = self.block(statements, statements_span)?;
                    let value = self.from_ast_expr(value)?;
                    result = Some(self.declare_var(name, value, declare_span, is_const, block)?);
                    last_pos = pos;
                }
                let mut statements: Vec<Expression> = statements[..last_pos].iter()
                    .map(|statement| self.from_ast_expr(statement))
                    .collect::<Result<_, _>>()?;
                if let Some(result) = result {
                    statements.push(result);
                }
                self.block(statements, ast.span)
            },
            AstExpressionKind::Int(s) => self.int_literal(s.replace("_", ""), ast.span),
            AstExpressionKind::Float(s) => self.float_literal(s.replace("_", ""), ast.span),
            AstExpressionKind::StringLiteral(s) => self.string_literal(s.clone(), ast.span),
            AstExpressionKind::Bool(b) => self.bool_literal(*b, ast.span),
            AstExpressionKind::PrefixUnaryOperation(op, expr) => {
                let op = op.as_ref().map(|inner| match inner.as_str() {
                    "-" => UnaryOperator::Minus,
                    "!" => UnaryOperator::Not,
                    _ => todo!("Unsupported unary operator: {}", inner)
                });
                let expr = self.from_ast_expr(expr)?;
                self.prefix_unary_op(op, expr, ast.span)
            },
            AstExpressionKind::Variable(name) => self.variable(name.clone(), ast.span),
            AstExpressionKind::PostfixUnaryOperation(_, _) => todo!("Postfix unary operations not yet supported"),
            AstExpressionKind::Assignment(name, expr) => {
                let expr = self.from_ast_expr(expr)?;
                self.assignment(name.clone(), expr, ast.span)
            },
            AstExpressionKind::Let(_, _) | AstExpressionKind::Var(_, _) => {
                panic!("Let/Var expressions should be handled in Block")
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::span::{Span, Spanned};

    fn default_span() -> Span {
        Span::default()
    }

    #[test]
    fn test_make_hir_expr_binary_operation() {
        let span = default_span();
        let left = AstExpression::new(AstExpressionKind::int("5"), span);
        let right = AstExpression::new(AstExpressionKind::int("3"), span);
        let op = Spanned::new("+".to_string(), span);
        let expr = AstExpression::new(AstExpressionKind::binary_operation(left, op, right), span);

        let mut hir_maker = Maker::new();
        let result = hir_maker.from_ast_expr(&expr);

        assert!(result.is_ok());
        let result = result.unwrap();
        match result.kind {
            ExpressionKind::BinaryOp { op, left, right } => {
                assert_eq!(op.inner, BinaryOperator::Add);
                match left.kind {
                    ExpressionKind::Literal(Literal::Int(n)) => assert_eq!(n.as_ref(), "5"),
                    _ => panic!("Expected Int literal"),
                }
                match right.kind {
                    ExpressionKind::Literal(Literal::Int(n)) => assert_eq!(n.as_ref(), "3"),
                    _ => panic!("Expected Int literal"),
                }
            },
            _ => panic!("Expected BinaryOp"),
        }
    }

    #[test]
    fn test_make_hir_expr_block() {
        let span = default_span();
        let stmt1 = AstExpression::new(AstExpressionKind::int("1"), span);
        let stmt2 = AstExpression::new(AstExpressionKind::int("2"), span);
        let block = AstExpression::new(AstExpressionKind::block(vec![stmt1, stmt2]), span);

        let mut hir_maker = Maker::new();
        let result = hir_maker.from_ast_expr(&block);

        let result = result.unwrap();
        let ExpressionKind::Block { statements } = result.kind else { panic!("Expected Block") };
        
        assert_eq!(statements.len(), 2);
        match &statements[0].kind {
            ExpressionKind::Literal(Literal::Int(n)) => assert_eq!(n.as_ref(), "1"),
            _ => panic!("Expected Int literal"),
        }
        match &statements[1].kind {
            ExpressionKind::Literal(Literal::Int(n)) => assert_eq!(n.as_ref(), "2"),
            _ => panic!("Expected Int literal"),
        }
    }

    #[test]
    fn test_make_hir_expr_variable_declaration() {
        let span = default_span();
        let name = Spanned::new(Rc::from("x"), span);
        let value = AstExpression::new(AstExpressionKind::int("42"), span);
        let scope = AstExpression::new(AstExpressionKind::variable("x"), span);
        let let_ = AstExpression::new(
            AstExpressionKind::Let(name.clone(), Box::new(value)),
            span
        );
        let expr = AstExpression::new(AstExpressionKind::block(vec![let_, scope]), span);

        let mut hir_maker = Maker::new();
        let result = hir_maker.from_ast_expr(&expr);

        assert!(result.is_ok());
        let result = result.unwrap();
        let ExpressionKind::Block { statements } = result.kind else { panic!("Expected Block") };
        assert_eq!(statements.len(), 1);

        let ExpressionKind::DeclareVar { is_const, name, value, scope } = &statements[0].kind else { panic!("Expected DeclareVar") };
        assert_eq!(*is_const, true);
        assert_eq!(hir_maker.symbol_arena.get_name(&name.inner).unwrap().as_ref(), "x");
        match &value.kind {
            ExpressionKind::Literal(Literal::Int(n)) => assert_eq!(n.as_ref(), "42"),
            _ => panic!("Expected Int literal"),
        }
        let ExpressionKind::Block { statements: inner_statements } = &scope.kind else { panic!("Expected Block") };
        assert_eq!(inner_statements.len(), 1);
        match &inner_statements[0].kind {
            ExpressionKind::Variable { name } => assert_eq!(hir_maker.symbol_arena.get_name(name).unwrap().as_ref(), "x"),
            _ => panic!("Expected Variable"),
        }
    }
} 