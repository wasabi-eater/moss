use crate::span::Span;
use crate::thir;
use crate::types::{Type, TypeVar, VarMaker};
use crate::hir;
use std::fmt;
use crate::errors::Error;
use std::collections::HashMap;
use itertools::Itertools;
use std::rc::Rc;
use literally::hmap;
use crate::symbol::Symbol;

#[derive(PartialEq)]
pub struct Subst {
    subst: HashMap<TypeVar, Type>,
}
impl Subst {
    pub fn new() -> Self {
        Subst { subst: HashMap::new() }
    }
    pub fn get_type(&self, var: TypeVar) -> Option<Type> {
        self.subst.get(&var).cloned()
    }
    pub fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Primitive(_) => ty.clone(),
            &Type::TypeVar(var) => self.get_type(var).unwrap_or(Type::TypeVar(var)),
            Type::Unknown => ty.clone(),
            Type::FuncPointer(params, ret) =>
                Type::FuncPointer(params.iter().map(|param| self.apply(param)).collect(), Rc::new(self.apply(ret)))
        }
    }
    pub fn insert(&mut self, var: TypeVar, ty: Type) {
        self.subst.insert(var, ty);
    }
}
impl fmt::Debug for Subst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Subst{{ {} }}", self.subst.iter().map(|(var, ty)| format!("{var:?} = {ty:?}")).join(", "))
    }
}
#[derive(Debug, Clone)]
struct VarData {
    ty: Type,
    is_const: bool
}

pub(crate) struct Env {
    var_data: HashMap<Symbol, Vec<VarData>>,
    bin_op_types: HashMap<hir::BinaryOperator, HashMap<(Type, Type), Type>>,
    un_op_types: HashMap<hir::UnaryOperator, HashMap<Type, Type>>
}
impl Env {
    pub fn new() -> Self {
        Env {
            var_data: HashMap::new(),
            bin_op_types: hmap! {
                hir::BinaryOperator::Add => hmap! {
                    (Type::int(), Type::int()) => Type::int(),
                    (Type::float(), Type::float()) => Type::float(),
                    (Type::string(), Type::string()) => Type::string()
                },
                hir::BinaryOperator::Subtract => hmap! {
                    (Type::int(), Type::int()) => Type::int(),
                    (Type::float(), Type::float()) => Type::float()
                },
                hir::BinaryOperator::Multiply => hmap! {
                    (Type::int(), Type::int()) => Type::int(),
                    (Type::float(), Type::float()) => Type::float()
                },
                hir::BinaryOperator::Divide => hmap! {
                    (Type::int(), Type::int()) => Type::int(),
                    (Type::float(), Type::float()) => Type::float()
                },
            },
            un_op_types: hmap! {
                hir::UnaryOperator::Minus => hmap! {
                    Type::int() => Type::int(),
                    Type::float() => Type::float()
                },
                hir::UnaryOperator::Not => hmap! {
                    Type::bool() => Type::bool()
                }
            }
        }
    }
}

pub(crate) struct Infer {
    pub errors: Vec<Error>,
    env: Env,
    subst: Subst,
    var_type_maker: VarMaker,
}
impl Infer {
    pub fn new(env: Env) -> Self {
        Self {
            errors: vec![],
            env,
            subst: Subst::new(),
            var_type_maker: VarMaker::new()
        }
    }
    fn error(&mut self, err: Error) {
        self.errors.push(err);
    }
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }
    pub fn infer_with_errors(&mut self, hir: &hir::Expression) -> (Option<thir::Expression>, Vec<Error>) {
        let result = self.infer(hir);
        (Some(result), self.errors.clone())
    }
    fn get_var_data(&mut self, symbol: Symbol) -> Option<VarData> {
        self.env.var_data.get(&symbol).and_then(|data| data.last().cloned())
    }
    fn get_var_type(&mut self, symbol: Symbol, span: Span) -> Type {
        match self.get_var_data(symbol.clone()) {
            Some(data) => data.ty,
            None => {
                self.error(Error::underfined_var(symbol, span));
                Type::Unknown
            }
        }
    }
    fn new_type_var(&mut self) -> TypeVar {
        self.var_type_maker.new_var()
    }
    fn bin_op_types(&self, op: hir::BinaryOperator) -> &HashMap<(Type, Type), Type> {
        &self.env.bin_op_types[&op]
    }
    fn un_op_types(&self, op: hir::UnaryOperator) -> &HashMap<Type, Type> {
        &self.env.un_op_types[&op]
    }
    fn unify(&mut self, found: Type, expected: Type, span: Span) {
        match (found, expected) {
            (Type::Primitive(p1), Type::Primitive(p2)) if p1 == p2 => {},
            (Type::TypeVar(var), ty) | (ty, Type::TypeVar(var)) => self.unify_var(var, ty, span),
            (Type::Unknown, _) | (_, Type::Unknown) => {},
            (found, expected) => self.error(Error::type_mismatch(expected, found, span)),
        }
    }
    fn unify_var(&mut self, var: TypeVar, ty: Type, span: Span) {
        if ty == Type::TypeVar(var) { return; }
        if ty.free_vars().contains(&var) {
            self.error(Error::occurs_check_error(var, ty, span));
        } else {
            self.subst.insert(var, ty);
        }
    }
    pub fn infer(&mut self, hir: &hir::Expression) -> thir::Expression {
        let span = hir.span;
        match &hir.kind {
            hir::ExpressionKind::Literal(lit) => {
                let ty = match lit {
                    hir::Literal::Int(_) => Type::int(),
                    hir::Literal::Float(_) => Type::float(),
                    hir::Literal::String(_) => Type::string(),
                    hir::Literal::Bool(_) => Type::bool(),
                };
                let lit = match lit.clone() {
                    hir::Literal::Int(n) => thir::Literal::Int(n),
                    hir::Literal::Bool(b) => thir::Literal::Bool(b),
                    hir::Literal::Float(f) => thir::Literal::Float(f),
                    hir::Literal::String(s) => thir::Literal::String(s)
                };
                thir::Expression {
                    kind: thir::ExpressionKind::Literal(lit),
                    type_: ty,
                    span
                }
            }
            hir::ExpressionKind::Variable { name } => {
                let var_type = self.get_var_type(name.clone(), span);
                thir::Expression {
                    kind: thir::ExpressionKind::Variable { name: name.clone() },
                    type_: self.subst.apply(&var_type),
                    span
                }
            }
            hir::ExpressionKind::Block { statements } =>{
                let statements =
                    statements.iter()
                    .map(|expr| self.infer(&expr))
                    .collect_vec();
                let ty = match statements.last() {
                    Some(last_expr) => last_expr.type_.clone(),
                    None => Type::unit()
                };
                thir::Expression {
                    kind: thir::ExpressionKind::Block { statements },
                    type_: ty,
                    span
                }
            }
            hir::ExpressionKind::Assignment { name, value } => {
                let var_type = self.get_var_type(name.inner.clone(), span);
                let value = self.infer(&*&value);
                self.unify(value.type_.clone(), var_type, span);
                if self.get_var_data(name.inner.clone()).map(|data| data.is_const) == Some(true) {
                    self.error(Error::assign_const_var(name.clone(), span));
                }
                thir::Expression {
                    kind: thir::ExpressionKind::Assingment { var_name: name.clone(), value: Box::new(value) },
                    type_: Type::unit(),
                    span
                }
            },
            hir::ExpressionKind::DeclareVar { is_const, name, value , scope} => {
                let var_type = self.new_type_var();
                let value = self.infer(value);
                self.env.var_data.entry(name.inner.clone()).or_insert(vec![]).push(VarData { ty: Type::TypeVar(var_type), is_const: *is_const });
                self.unify(value.type_.clone(), Type::TypeVar(var_type), span);
                let scope = self.infer(scope);
                self.env.var_data.get_mut(&name.inner).unwrap().pop();
                let ty = scope.type_.clone();
                thir::Expression {
                    kind: thir::ExpressionKind::DeclareVar {
                        is_const: *is_const,
                        name: name.clone(),
                        value: Box::new(value),
                        scope: Box::new(scope)
                    },
                    type_: ty,
                    span
                }
            },
            hir::ExpressionKind::BinaryOp { op, left, right } => {
                let left = self.infer(left);
                let right = self.infer(right);
                let op_types = self.bin_op_types(op.inner);
                
                let ty = if left.type_ == Type::Unknown || right.type_ == Type::Unknown {
                    Type::Unknown
                }
                else {
                    op_types.get(&(left.type_.clone(), right.type_.clone())).cloned().unwrap_or_else(|| {
                        self.error(Error::invalid_bin_op(op.clone(), left.type_.clone(), right.type_.clone(), span));
                        Type::Unknown
                    })
                };
                thir::Expression {
                    kind: thir::ExpressionKind::BinaryOp { left: Box::new(left), op: op.clone(), right: Box::new(right) },
                    type_: ty,
                    span
                }
            },
            hir::ExpressionKind::PrefixUnaryOp { op, operand } => {
                let operand = self.infer(operand);
                let op_types = self.un_op_types(op.inner);
                let ty = if operand.type_ == Type::Unknown {
                    Type::Unknown
                }
                else {
                    op_types.get(&operand.type_).cloned().unwrap_or_else(|| {
                        self.error(Error::invalid_un_op(op.clone(), operand.type_.clone(), span));
                        Type::Unknown
                    })
                };
                thir::Expression {
                    kind: thir::ExpressionKind::PrefixUnaryOp {
                        op: op.clone(),
                        operand: Box::new(operand)
                    },
                    span,
                    type_: ty
                }
            },
            hir::ExpressionKind::If { cond, then, otherwise } => {
                let cond = self.infer(cond);
                let then = self.infer(then);
                let otherwise = otherwise.as_ref().map(|otherwise| self.infer(otherwise));
                let ty = then.type_.clone();
                if let Some(otherwise) = otherwise {
                    self.unify(otherwise.type_.clone(), ty.clone(), span);    
                    thir::Expression {
                        kind: thir::ExpressionKind::If { cond: Box::new(cond), then: Box::new(then), otherwise: Some(Box::new(otherwise)) },
                        type_: ty,
                        span
                    }
                }
                else {
                    thir::Expression {
                        kind: thir::ExpressionKind::If { cond: Box::new(cond), then: Box::new(then), otherwise: None },
                        type_: Type::unit(),
                        span
                    }
                }
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use crate::span::{Span, Spanned};

    use crate::{hir::{self, Expression as HirExpression, ExpressionKind as HirExpressionKind, Literal as HirLiteral}, thir};

    use super::*;

    #[test]
    fn test_infer_literal_int() {
        let expr = HirExpression {
            kind: HirExpressionKind::Literal(HirLiteral::Int("42".into())),
            span: Span::default(),
        };
        let mut infer = Infer::new(Env::new());
        assert_eq!(infer.infer(&expr), thir::Expression {
            kind: thir::ExpressionKind::Literal(thir::Literal::Int("42".into())),
            span: Span::default(),
            type_: Type::int()
        });
        assert!(infer.errors.is_empty());
    }

    #[test]
    fn test_infer_literal_float() {
        let expr = HirExpression {
            kind: HirExpressionKind::Literal(HirLiteral::Float("3.14".into())),
            span: Span::default(),
        };
        let mut infer = Infer::new(Env::new());
        assert_eq!(infer.infer(&expr), thir::Expression {
            kind: thir::ExpressionKind::Literal(thir::Literal::Float("3.14".into())),
            span: Span::default(),
            type_: Type::float()
        });
        assert!(infer.errors.is_empty());
    }

    #[test]
    fn test_infer_literal_string() {
        let expr = HirExpression {
            kind: HirExpressionKind::Literal(HirLiteral::String("hello".into())),
            span: Span::default(),
        };
        let mut infer = Infer::new(Env::new());
        assert_eq!(infer.infer(&expr), thir::Expression {
            kind: thir::ExpressionKind::Literal(thir::Literal::String("hello".into())),
            span: Span::default(),
            type_: Type::string()
        });
        assert!(infer.errors.is_empty());
    }

    #[test]
    fn test_infer_literal_bool() {
        let expr = HirExpression {
            kind: HirExpressionKind::Literal(HirLiteral::Bool(true)),
            span: Span::default(),
        };
        let mut infer = Infer::new(Env::new());
        assert_eq!(infer.infer(&expr), thir::Expression {
            kind: thir::ExpressionKind::Literal(thir::Literal::Bool(true)),
            span: Span::default(),
            type_: Type::bool()
        });
        assert!(infer.errors.is_empty())
    }

    #[test]
    fn test_infer_binary_op_add_ints() {
        let left = Box::new(HirExpression {
            kind: HirExpressionKind::Literal(HirLiteral::Int("1".into())),
            span: Span::default(),
        });
        let right = Box::new(HirExpression {
            kind: HirExpressionKind::Literal(HirLiteral::Int("2".into())),
            span: Span::default(),
        });
        let expr = HirExpression {
            kind: HirExpressionKind::BinaryOp {
                op: Spanned::new(hir::BinaryOperator::Add, Span::default()),
                left,
                right,
            },
            span: Span::default(),
        };
        let mut infer = Infer::new(Env::new());
        assert_eq!(infer.infer(&expr), thir::Expression {
            kind: thir::ExpressionKind::BinaryOp {
                left: Box::new(thir::Expression {
                    kind: thir::ExpressionKind::Literal(thir::Literal::Int("1".into())),
                    span: Span::default(),
                    type_: Type::int()
                }),
                op: Spanned::new(hir::BinaryOperator::Add, Span::default()),
                right: Box::new(thir::Expression {
                    kind: thir::ExpressionKind::Literal(thir::Literal::Int("2".into())),
                    span: Span::default(),
                    type_: Type::int()
                })
            },
            type_: Type::int(),
            span: Span::default()
        });
        assert!(infer.errors.is_empty());
    }

    #[test]
    fn test_infer_binary_op_add_floats() {
        let left = Box::new(HirExpression {
            kind: HirExpressionKind::Literal(HirLiteral::Float("1.0".into())),
            span: Span::default(),
        });
        let right = Box::new(HirExpression {
            kind: HirExpressionKind::Literal(HirLiteral::Float("2.0".into())),
            span: Span::default(),
        });
        let expr = HirExpression {
            kind: HirExpressionKind::BinaryOp {
                op: Spanned::new(hir::BinaryOperator::Add, Span::default()),
                left,
                right,
            },
            span: Span::default(),
        };
        let mut infer = Infer::new(Env::new());
        assert_eq!(infer.infer(&expr), thir::Expression {
            kind: thir::ExpressionKind::BinaryOp {
                left: Box::new(thir::Expression {
                    kind: thir::ExpressionKind::Literal(thir::Literal::Float("1.0".into())),
                    span: Span::default(),
                    type_: Type::float()
                }),
                op: Spanned::new(hir::BinaryOperator::Add, Span::default()),
                right: Box::new(thir::Expression {
                    kind: thir::ExpressionKind::Literal(thir::Literal::Float("2.0".into())),
                    span: Span::default(),
                    type_: Type::float()
                })
            },
            type_: Type::float(),
            span: Span::default()
        });
    }

    #[test]
    fn test_infer_assignment() {
        let span = Span::default();
        let mut hir_maker = hir::Maker::new();
        let value = hir_maker.int_literal("10", span).unwrap();
        let var = hir_maker.variable(Rc::from("x"), span).unwrap();
        let expr = hir_maker.declare_var(
            Spanned::new(Rc::from("x"), span),
            value,
            span,
            true,
            var
        ).unwrap();
        let mut infer = Infer::new(Env::new());
        let name = hir_maker.symbol_arena.symbol("x");
        assert_eq!(infer.infer(&expr), thir::Expression {
            kind: thir::ExpressionKind::DeclareVar {
                is_const: true,
                name: Spanned::new(name.clone(), span),
                value: Box::new(thir::Expression {
                    kind: thir::ExpressionKind::Literal(thir::Literal::Int("10".into())),
                    type_: Type::int(),
                    span
                }), 
                scope: Box::new(thir::Expression {
                    kind: thir::ExpressionKind::Variable { name },
                    span,
                    type_: Type::int()
                })
            },
            type_: Type::int(),
            span
        });
        assert!(infer.errors.is_empty());
    }

    #[test]
    fn test_error_messages() {
        let span = Span::default();
        let mut hir_maker = hir::Maker::new();
        
        let expr = hir_maker.variable(Rc::from("undefined"), span).unwrap();
        let mut infer = Infer::new(Env::new());
        
        let (result, errors) = infer.infer_with_errors(&expr);
        assert!(result.is_some());
        assert_eq!(errors.len(), 1);
        
        let error_messages = infer.errors.iter().map(|e| e.message(&hir_maker.symbol_arena)).collect_vec();
        assert_eq!(error_messages.len(), 1);
        assert!(error_messages[0].contains("未定義の変数"));
    }

    #[test]
    fn test_type_mismatch_error() {
        let span = Span::default();
        let mut hir_maker = hir::Maker::new();
        
        let left = hir_maker.string_literal(Rc::from("hello"), span).unwrap();
        let right = hir_maker.int_literal("42", span).unwrap();
        let expr = hir_maker.binary_op(
            Spanned::new(hir::BinaryOperator::Add, span),
            left,
            right,
            span
        ).unwrap();
        
        let mut infer = Infer::new(Env::new());
        
        let (result, errors) = infer.infer_with_errors(&expr);
        assert!(result.is_some());
        assert_eq!(errors.len(), 1);
        
        let error_messages = infer.errors.iter().map(|e| e.message(&hir_maker.symbol_arena)).collect_vec();
        assert_eq!(error_messages.len(), 1);
        assert!(error_messages[0].contains("無効な二項演算"));
    }
    #[test]
    fn test_infer_if_expression_with_else() {
        let span = Span::default();
        let mut hir_maker = hir::Maker::new();

        let cond = hir_maker.bool_literal(true, span).unwrap();
        let then_branch = hir_maker.int_literal("1", span).unwrap();
        let else_branch = hir_maker.int_literal("2", span).unwrap();

        let expr = hir_maker.if_(cond.clone(), then_branch.clone(), Some(else_branch.clone()), span).unwrap();

        let mut infer = Infer::new(Env::new());
        let thir_expr = infer.infer(&expr);

        assert_eq!(
            thir_expr,
            thir::Expression {
                kind: thir::ExpressionKind::If {
                    cond: Box::new(thir::Expression {
                        kind: thir::ExpressionKind::Literal(thir::Literal::Bool(true)),
                        type_: Type::bool(),
                        span,
                    }),
                    then: Box::new(thir::Expression {
                        kind: thir::ExpressionKind::Literal(thir::Literal::Int("1".into())),
                        type_: Type::int(),
                        span,
                    }),
                    otherwise: Some(Box::new(thir::Expression {
                        kind: thir::ExpressionKind::Literal(thir::Literal::Int("2".into())),
                        type_: Type::int(),
                        span,
                    })),
                },
                type_: Type::int(),
                span,
            }
        );
        assert!(infer.errors.is_empty());
    }

    #[test]
    fn test_infer_if_expression_without_else() {
        let span = Span::default();
        let mut hir_maker = hir::Maker::new();

        let cond = hir_maker.bool_literal(false, span).unwrap();
        let then_branch = hir_maker.string_literal(Rc::from("then"), span).unwrap();

        let expr = hir_maker.if_(cond.clone(), then_branch.clone(), None, span).unwrap();

        let mut infer = Infer::new(Env::new());
        let thir_expr = infer.infer(&expr);

        assert_eq!(
            thir_expr,
            thir::Expression {
                kind: thir::ExpressionKind::If {
                    cond: Box::new(thir::Expression {
                        kind: thir::ExpressionKind::Literal(thir::Literal::Bool(false)),
                        type_: Type::bool(),
                        span,
                    }),
                    then: Box::new(thir::Expression {
                        kind: thir::ExpressionKind::Literal(thir::Literal::String("then".into())),
                        type_: Type::string(),
                        span,
                    }),
                    otherwise: None,
                },
                type_: Type::unit(),
                span,
            }
        );
        assert!(infer.errors.is_empty());
    }

    #[test]
    fn test_infer_if_expression_type_mismatch_error() {
        let span = Span::default();
        let mut hir_maker = hir::Maker::new();

        let cond = hir_maker.bool_literal(true, span).unwrap();
        let then_branch = hir_maker.int_literal("1", span).unwrap();
        let else_branch = hir_maker.string_literal(Rc::from("else"), span).unwrap();

        let expr = hir_maker.if_(cond.clone(), then_branch.clone(), Some(else_branch.clone()), span).unwrap();

        let mut infer = Infer::new(Env::new());
        let (_result, errors) = infer.infer_with_errors(&expr);

        assert_eq!(errors.len(), 1);
        let error_messages = infer.errors.iter().map(|e| e.message(&hir_maker.symbol_arena)).collect_vec();
        assert!(error_messages[0].contains("型が一致しません") || error_messages[0].contains("型"));
    }
}