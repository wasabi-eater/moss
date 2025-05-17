use std::collections::{HashMap, LinkedList};
use crate::{
    hir,
    types::Type,
    thir::{Expression, ExpressionKind, Literal as ThirLiteral},
    symbol::Symbol
};
use super::core::*;

/// THIRからMIRへの変換を行うための構造体
pub(crate) struct Maker {
    place_maker: PlaceMaker,
    types: HashMap<Place, Type>,
    is_const: HashMap<Place, bool>,
    id_place_map: HashMap<Symbol, Vec<Place>>
}

impl Maker {    
    /// THIRの式からMIRのエントリーポイントを生成します
    pub(crate) fn entry_point(expr: Expression) -> EntryPoint {
        let mut maker = Maker {
            place_maker: PlaceMaker::new(),
            types: HashMap::new(),
            is_const: HashMap::new(),
            id_place_map: HashMap::new()
        };
        let mut statements = LinkedList::new();
        let place = maker.place_maker.make();
        maker.write_sequential_statements(expr, &mut statements, place);
        statements.push_back(Statement::Drop(Operand(place)));
        let seq = SequentialExecution {
            statements
        };
        EntryPoint {
            types: maker.types,
            seq,
            is_const: maker.is_const
        }
    }

    /// THIRの式をMIRの文の列に変換します
    fn write_sequential_statements(&mut self, expr: Expression, execs: &mut LinkedList<Statement>, place: Place) {
        self.types.insert(place, expr.type_.clone());
        match expr.kind {
            ExpressionKind::DeclareVar { is_const, name, value, scope } => {
                let var_place = self.place_maker.make();
                self.write_sequential_statements(*value, execs, var_place);
                self.id_place_map.entry(name.inner.clone()).or_insert(vec![]).push(var_place);
                self.is_const.insert(var_place, is_const);
                self.types.insert(var_place, expr.type_);
                self.write_sequential_statements(*scope, execs, place);
                self.id_place_map.get_mut(&name.inner).expect(&format!("{:?} was lost", name.inner)).pop();
            }
            ExpressionKind::Assingment { var_name, value } => {
                let tmp_place = self.place_maker.make();
                let var_place = *self.id_place_map.get(&var_name.inner)
                    .and_then(|places| places.last())
                    .expect("無効なIDです");
                self.write_sequential_statements(*value, execs, tmp_place);
                execs.push_back(Statement::CopyAssign { from: Operand(tmp_place), to: var_place });
                execs.push_back(Statement::Expr(Rvalue::Literal(place, Literal::Unit)));
            }
            ExpressionKind::BinaryOp { left, op, right } => {
                let left_place = self.place_maker.make();
                let right_place = self.place_maker.make();
                let left_type = left.type_.clone();
                let right_type = right.type_.clone();
                self.write_sequential_statements(*left, execs, left_place);
                self.write_sequential_statements(*right, execs, right_place);
                let op = match op.inner {
                    hir::BinaryOperator::Add => BinaryOperator::Add(left_type, right_type),
                    hir::BinaryOperator::Subtract => BinaryOperator::Subtract(left_type, right_type),
                    hir::BinaryOperator::Multiply => BinaryOperator::Multiply(left_type, right_type),
                    hir::BinaryOperator::Divide => BinaryOperator::Divide(left_type, right_type),
                    hir::BinaryOperator::Equal => BinaryOperator::Equal(left_type, right_type),
                    hir::BinaryOperator::NotEqual => BinaryOperator::NotEqual(left_type, right_type),
                    hir::BinaryOperator::GreaterThan => BinaryOperator::GreaterThan(left_type, right_type),
                    hir::BinaryOperator::GreaterThanOrEqual => BinaryOperator::GreaterThanOrEqual(left_type, right_type),
                    hir::BinaryOperator::LessThan => BinaryOperator::LessThan(left_type, right_type),
                    hir::BinaryOperator::LessThanOrEqual => BinaryOperator::LessThanOrEqual(left_type, right_type),
                    hir::BinaryOperator::And => BinaryOperator::And(left_type, right_type),
                    hir::BinaryOperator::Or => BinaryOperator::Or(left_type, right_type),
                    hir::BinaryOperator::Xor => BinaryOperator::Xor(left_type, right_type)
                };
                execs.push_back(Statement::Expr(Rvalue::BinaryOp(place, Operand(left_place), op, Operand(right_place))));
            }
            ExpressionKind::Block { mut statements } => {
                let Some(last_statement) = statements.pop() else {
                    execs.push_back(Statement::Expr(Rvalue::Literal(place, Literal::Unit)));
                    return
                };
                for statement in statements {
                    let dropped_place = self.place_maker.make();
                    self.write_sequential_statements(statement, execs, dropped_place);
                }
                self.write_sequential_statements(last_statement, execs, place);
            },
            ExpressionKind::Literal(lit) => {
                let lit = match lit {
                    ThirLiteral::Bool(b) => Literal::Bool(b),
                    ThirLiteral::Int(i) => Literal::Int(i),
                    ThirLiteral::Float(f) => Literal::Float(f),
                    ThirLiteral::String(s) => Literal::String(s),
                };
                execs.push_back(Statement::Expr(Rvalue::Literal(place, lit)));
            }
            ExpressionKind::PrefixUnaryOp { op, operand } => {
                let op = match op.inner {
                    hir::UnaryOperator::Minus => UnaryOperator::Minus(operand.type_.clone()),
                    hir::UnaryOperator::Not => UnaryOperator::Not(operand.type_.clone())
                };
                let operand_place = self.place_maker.make();
                self.write_sequential_statements(*operand, execs, operand_place);
                execs.push_back(Statement::Expr(Rvalue::UnaryOperator(place, op, Operand(operand_place))));
            },
            ExpressionKind::Variable { name } => {
                let var_place = *self.id_place_map[&name].last().expect(&format!("Invalid {name:?}"));
                execs.push_back(Statement::CopyBinding { from: Operand(var_place), to: place });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolArena;
    use crate::span::{Span, Spanned};
    use crate::hir::{BinaryOperator as HirBinaryOperator};
    use crate::thir::{Expression, ExpressionKind, Literal as ThirLiteral};

    fn default_span() -> Span {
        Span::default()
    }

    fn setup_test() -> (PlaceMaker, LinkedList<Statement>) {
        (PlaceMaker::new(), LinkedList::new())
    }

    #[test]
    fn test_literal_conversion() {
        let expr = Expression {
            kind: ExpressionKind::Literal(ThirLiteral::Int("42".into())),
            span: default_span(),
            type_: Type::int()
        };

        let entry_point = Maker::entry_point(expr);
        
        // MIRの内容を確認
        let (_, mut expected) = setup_test();
        let mut place_maker = PlaceMaker::new();
        let place = place_maker.make();
        expected.push_back(Statement::Expr(Rvalue::Literal(place, Literal::Int("42".into()))));
        expected.push_back(Statement::Drop(Operand(place)));

        assert_eq!(entry_point.seq.statements, expected);
        assert_eq!(entry_point.types.get(&place), Some(&Type::int()));
    }

    #[test]
    fn test_binary_operation() {
        let expr = Expression {
            kind: ExpressionKind::BinaryOp {
                left: Box::new(Expression {
                    kind: ExpressionKind::Literal(ThirLiteral::Int("10".into())),
                    span: default_span(),
                    type_: Type::int()
                }),
                op: Spanned {
                    inner: HirBinaryOperator::Add,
                    span: default_span()
                },
                right: Box::new(Expression {
                    kind: ExpressionKind::Literal(ThirLiteral::Int("20".into())),
                    span: default_span(),
                    type_: Type::int()
                })
            },
            span: default_span(),
            type_: Type::int()
        };

        let entry_point = Maker::entry_point(expr);
        
        // MIRの内容を確認
        let (_, mut expected) = setup_test();
        let mut place_maker = PlaceMaker::new();
        let result_place = place_maker.make();
        let left_place = place_maker.make();
        let right_place = place_maker.make();

        expected.push_back(Statement::Expr(Rvalue::Literal(left_place, Literal::Int("10".into()))));
        expected.push_back(Statement::Expr(Rvalue::Literal(right_place, Literal::Int("20".into()))));
        expected.push_back(Statement::Expr(Rvalue::BinaryOp(
            result_place,
            Operand(left_place),
            BinaryOperator::Add(Type::int(), Type::int()),
            Operand(right_place)
        )));
        expected.push_back(Statement::Drop(Operand(result_place)));

        assert_eq!(entry_point.seq.statements, expected);
        assert_eq!(entry_point.types.get(&left_place), Some(&Type::int()));
        assert_eq!(entry_point.types.get(&right_place), Some(&Type::int()));
        assert_eq!(entry_point.types.get(&result_place), Some(&Type::int()));
    }

    #[test]
    fn test_variable_declaration() {
        let mut symbol_arena = SymbolArena::new();
        let expr = Expression {
            kind: ExpressionKind::DeclareVar {
                is_const: true,
                name: Spanned {
                    inner: symbol_arena.symbol("a".to_string()),
                    span: default_span()
                },
                value: Box::new(Expression {
                    kind: ExpressionKind::Literal(ThirLiteral::Int("100".into())),
                    span: default_span(),
                    type_: Type::int()
                }),
                scope: Box::new(Expression {
                    kind: ExpressionKind::Variable {
                        name: symbol_arena.symbol("a".to_string())
                    },
                    span: default_span(),
                    type_: Type::int()
                })
            },
            span: default_span(),
            type_: Type::int()
        };

        let entry_point = Maker::entry_point(expr);
        
        // MIRの内容を確認
        let (_, mut expected) = setup_test();
        let mut place_maker = PlaceMaker::new();
        let result_place = place_maker.make();
        let var_place = place_maker.make();

        expected.push_back(Statement::Expr(Rvalue::Literal(var_place, Literal::Int("100".into()))));
        expected.push_back(Statement::CopyBinding { from: Operand(var_place), to: result_place });
        expected.push_back(Statement::Drop(Operand(result_place)));

        assert_eq!(entry_point.seq.statements, expected);
        assert_eq!(entry_point.types.get(&var_place), Some(&Type::int()));
        assert_eq!(entry_point.types.get(&result_place), Some(&Type::int()));
        assert!(entry_point.is_const.get(&var_place).unwrap());
    }
} 