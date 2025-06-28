use std::collections::{HashMap, VecDeque};
use crate::{
    hir, symbol::Symbol, thir::{Expression, ExpressionKind, Literal as ThirLiteral}, metadata::types::Type
};
use super::core::*;
use literally::vecd;
use typed_arena::Arena;

pub(crate) enum SeqBlockBuilder {
    Statement(Statement),
    If(Operand, Vec<SeqBlockBuilder>, Vec<SeqBlockBuilder>),
    Return(Operand)
}
impl SeqBlockBuilder {
    fn build_with_terminator<'blk>(mut builder_list: Vec<Self>, mut terminator: Terminator<'blk>, arena: &'blk Arena<SeqBlock<'blk>>) -> &'blk SeqBlock<'blk> {
        let mut statements = VecDeque::new();
        while let Some(builder) = builder_list.pop() {
            match builder {
                SeqBlockBuilder::Return(operand) => terminator = Terminator::Return(operand),
                SeqBlockBuilder::If(cond, then, otherwise) => {
                    if !statements.is_empty() {
                        let block = arena.alloc(SeqBlock::new(
                            statements,
                            terminator
                        ));
                        terminator = Terminator::Goto(block);
                        statements = vecd![];
                    }
                    let then = SeqBlockBuilder::build_with_terminator(then, terminator.shallow_clone(), arena);
                    let otherwise = SeqBlockBuilder::build_with_terminator(otherwise, terminator, arena);
                    terminator = Terminator::IfElse { cond, then, otherwise };
                }
                SeqBlockBuilder::Statement(statement) => statements.push_front(statement),
            }
        }
        arena.alloc(SeqBlock::new(
            statements,
            terminator
        ))
    }
    fn set_preblocks<'blk>(block: &'blk SeqBlock<'blk>) {
        match &*block.terminator.borrow() {
            Terminator::Goto(next_block) => {
                if next_block.preblocks.borrow_mut().insert(block) {
                    Self::set_preblocks(next_block);
                }
            }
            Terminator::Return(_) => { }
            Terminator::IfElse { cond: _, then, otherwise } => {
                let then_inserted = then.preblocks.borrow_mut().insert(block);
                let otherwise_inserted = otherwise.preblocks.borrow_mut().insert(block);
                if then_inserted {
                    Self::set_preblocks(then);
                }
                if otherwise_inserted {
                    Self::set_preblocks(otherwise);
                }
            }
        }
    }
    fn get_return_blocks<'blk>(block: &'blk SeqBlock<'blk>) -> Vec<&'blk SeqBlock<'blk>> {
        match &*block.terminator.borrow() {
            Terminator::Goto(next_block) => Self::get_return_blocks(next_block),
            Terminator::Return(_) => vec![block],
            Terminator::IfElse { cond: _, then, otherwise } => {
                let mut return_blocks = Self::get_return_blocks(then);
                return_blocks.append(&mut Self::get_return_blocks(otherwise));
                return_blocks
            }
        }
    }
}

/// THIRからMIRへの変換を行うための構造体
pub(crate) struct Maker<'blk> {
    place_maker: PlaceMaker,
    types: HashMap<Place, Type>,
    is_const: HashMap<Place, bool>,
    id_place_map: HashMap<Symbol, Vec<Place>>,
    block_arena: &'blk Arena<SeqBlock<'blk>>
}

impl<'blk> Maker<'blk> {
    /// THIRの式からMIRのエントリーポイントを生成します
    pub(crate) fn entry_point(expr: Expression, block_arena: &'blk Arena<SeqBlock<'blk>>) -> EntryPoint<'blk> {
        let mut maker = Maker {
            place_maker: PlaceMaker::new(),
            types: HashMap::new(),
            is_const: HashMap::new(),
            id_place_map: HashMap::new(),
            block_arena
        };
        let place = maker.place_maker.make();
        let blocks = maker.expr(expr, place);
        let built_block = SeqBlockBuilder::build_with_terminator(blocks, Terminator::Return(Operand(place)), block_arena);
        SeqBlockBuilder::set_preblocks(built_block);
        let return_blocks = SeqBlockBuilder::get_return_blocks(built_block);
        EntryPoint {
            seq_front: built_block,
            seq_backs: return_blocks,
            stack_env: StackEnv { types: maker.types, is_const: maker.is_const }
        }
    }

    /// THIRの式をMIRの文の列に変換します
    fn expr(&mut self, expr: Expression, place: Place) -> Vec<SeqBlockBuilder> {
        self.types.insert(place, expr.type_.clone());
        match expr.kind {
            ExpressionKind::DeclareVar { is_const, name, value, scope } =>
                self.declare_var(name.inner, *value, *scope, is_const, place),
            ExpressionKind::Assingment { var_name, value } =>
                self.assignment(var_name.inner, *value, place),
            ExpressionKind::BinaryOp { left, op, right } =>
                self.binary_op(*left, op.inner, *right, place),
            ExpressionKind::Block { statements } =>
                self.block(statements, place),
            ExpressionKind::Literal(lit) =>
                self.literal(lit, place),
            ExpressionKind::PrefixUnaryOp { op, operand } =>
                self.prefix_unary_op(op.inner, *operand, place),
            ExpressionKind::Variable { name } => self.variable(name, place),
            ExpressionKind::If { cond, then, otherwise } =>
                self.if_(*cond, *then, otherwise.map(|otherwise| *otherwise), place),
        }
    }
    fn declare_var(&mut self, name: Symbol, value: Expression, scope: Expression, is_const: bool, place: Place) -> Vec<SeqBlockBuilder> {
        let var_place = self.place_maker.make();
        let value_type = value.type_.clone();
        let mut blocks = self.expr(value, var_place);
        self.id_place_map.entry(name.clone()).or_insert(vec![]).push(var_place);
        self.is_const.insert(var_place, is_const);
        self.types.insert(var_place, value_type);
        blocks.append(&mut self.expr(scope, place));
        self.id_place_map.get_mut(&name).expect(&format!("{:?} was lost", name)).pop();
        blocks
    }
    fn assignment(&mut self, var_name: Symbol, value: Expression, place: Place) -> Vec<SeqBlockBuilder> {
        let tmp_place = self.place_maker.make();
        let var_place = *self.id_place_map.get(&var_name)
            .and_then(|places| places.last())
            .expect("無効なIDです");
        let mut blocks = self.expr(value, tmp_place);
        blocks.push(SeqBlockBuilder::Statement(Statement::CopyAssign { from: Operand(tmp_place), to: var_place }));
        blocks.push(SeqBlockBuilder::Statement(Statement::Expr(Rvalue::Literal(place, Literal::Unit))));
        blocks
    }
    fn binary_op(&mut self, left: Expression, op: hir::BinaryOperator, right: Expression, place: Place) -> Vec<SeqBlockBuilder> {
        let left_place = self.place_maker.make();
        let right_place = self.place_maker.make();
        let left_type = left.type_.clone();
        let right_type = right.type_.clone();
        let mut blocks = self.expr(left, left_place);
        blocks.append(&mut self.expr(right, right_place));
        let op = match op {
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
        blocks.push(SeqBlockBuilder::Statement(Statement::Expr(Rvalue::BinaryOp(place, Operand(left_place), op, Operand(right_place)))));
        blocks
    }
    fn block(&mut self, mut statements: Vec<Expression>, place: Place) -> Vec<SeqBlockBuilder> {
        let Some(last_statement) = statements.pop() else {
            return vec![
                SeqBlockBuilder::Statement(Statement::Expr(Rvalue::Literal(place, Literal::Unit)))
            ]
        };
        for statement in statements {
            let dropped_place = self.place_maker.make();
            self.expr(statement, dropped_place);
        }
        self.expr(last_statement, place)
    }
    fn literal(&mut self, lit: ThirLiteral, place: Place) -> Vec<SeqBlockBuilder> {
        let lit = match lit {
            ThirLiteral::Bool(b) => Literal::Bool(b),
            ThirLiteral::Int(i) => Literal::Int(i),
            ThirLiteral::Float(f) => Literal::Float(f),
            ThirLiteral::String(s) => Literal::String(s),
        };
        vec![SeqBlockBuilder::Statement(Statement::Expr(Rvalue::Literal(place, lit)))]
    }
    fn prefix_unary_op(&mut self, op: hir::UnaryOperator, operand: Expression, place: Place) -> Vec<SeqBlockBuilder> {
        let op = match op {
            hir::UnaryOperator::Minus => UnaryOperator::Minus(operand.type_.clone()),
            hir::UnaryOperator::Not => UnaryOperator::Not(operand.type_.clone())
        };
        let operand_place = self.place_maker.make();
        let mut blocks = self.expr(operand, operand_place);
        blocks.push(SeqBlockBuilder::Statement(Statement::Expr(Rvalue::UnaryOperator(place, op, Operand(operand_place)))));
        blocks
    }
    fn variable(&mut self, name: Symbol, place: Place) -> Vec<SeqBlockBuilder> {
        let var_place = *self.id_place_map[&name].last().expect(&format!("Invalid {name:?}"));
        vec![SeqBlockBuilder::Statement(Statement::CopyBinding { from: Operand(var_place), to: place })]
    }
    fn if_(&mut self, cond: Expression, then: Expression, otherwise: Option<Expression>, place: Place) -> Vec<SeqBlockBuilder> {
        let cond_place = self.place_maker.make();
        let mut blocks = self.expr(cond, cond_place);

        let then_blocks = self.expr(then, place);
        let otherwise_blocks = match otherwise {
            Some(otherwise) => self.expr(otherwise, place),
            None => vec![]
        };
        blocks.push(SeqBlockBuilder::If(
            Operand(cond_place),
            then_blocks,
            otherwise_blocks
        ));
        blocks
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

    fn setup_test() -> (PlaceMaker, VecDeque<Statement>) {
        (PlaceMaker::new(), VecDeque::new())
    }

    #[test]
    fn test_literal_conversion() {
        let expr = Expression {
            kind: ExpressionKind::Literal(ThirLiteral::Int("42".into())),
            span: default_span(),
            type_: Type::int()
        };

        let arena = Arena::new();
        let entry_point = Maker::entry_point(expr, &arena);
        
        // MIRの内容を確認
        let (_, mut expected_statements) = setup_test();
        let mut place_maker = PlaceMaker::new();
        let place = place_maker.make();
        expected_statements.push_back(Statement::Expr(Rvalue::Literal(place, Literal::Int("42".into()))));

        assert_eq!(&*entry_point.seq_front.statements.borrow(), &expected_statements);
        let Terminator::Return(Operand(place2)) = &*entry_point.seq_front.terminator.borrow() else {
            panic!("Expected a return terminator");
        };
        assert_eq!(place, *place2);
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
        let block_arena = Arena::new();
        let entry_point = Maker::entry_point(expr, &block_arena);
        
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

        assert_eq!(&*entry_point.seq_front.statements.borrow(), &expected);

        let types = entry_point.stack_env.types;
        assert_eq!(types.get(&left_place), Some(&Type::int()));
        assert_eq!(types.get(&right_place), Some(&Type::int()));
        assert_eq!(types.get(&result_place), Some(&Type::int()));
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

        let arena = Arena::new();
        let entry_point = Maker::entry_point(expr, &arena);
        
        // MIRの内容を確認
        let (_, mut expected) = setup_test();
        let mut place_maker = PlaceMaker::new();
        let result_place = place_maker.make();
        let var_place = place_maker.make();

        expected.push_back(Statement::Expr(Rvalue::Literal(var_place, Literal::Int("100".into()))));
        expected.push_back(Statement::CopyBinding { from: Operand(var_place), to: result_place });

        assert_eq!(&*entry_point.seq_front.statements.borrow(), &expected);
        let stack_env = entry_point.stack_env;
        let types = stack_env.types;
        assert_eq!(types.get(&var_place), Some(&Type::int()));
        assert_eq!(types.get(&result_place), Some(&Type::int()));
        assert!(stack_env.is_const.get(&var_place).unwrap());
    }
    #[test]
    fn test_if_expression() {
        let expr = Expression {
            kind: ExpressionKind::If {
                cond: Box::new(Expression {
                    kind: ExpressionKind::Literal(ThirLiteral::Bool(true)),
                    span: default_span(),
                    type_: Type::bool()
                }),
                then: Box::new(Expression {
                    kind: ExpressionKind::Literal(ThirLiteral::Int("1".into())),
                    span: default_span(),
                    type_: Type::int()
                }),
                otherwise: Some(Box::new(Expression {
                    kind: ExpressionKind::Literal(ThirLiteral::Int("0".into())),
                    span: default_span(),
                    type_: Type::int()
                }))
            },
            span: default_span(),
            type_: Type::int()
        };

        let arena = Arena::new();
        let entry_point = Maker::entry_point(expr, &arena);

        // MIRの内容を確認
        let mut place_maker = PlaceMaker::new();
        let result_place = place_maker.make();
        let cond_place = place_maker.make();

        // then/elseのplaceは同じresult_placeになる
        let then_expected = Statement::Expr(Rvalue::Literal(result_place, Literal::Int("1".into())));
        let else_expected = Statement::Expr(Rvalue::Literal(result_place, Literal::Int("0".into())));

        // condの評価
        let cond_stmt = Statement::Expr(Rvalue::Literal(cond_place, Literal::Bool(true)));

        let stmts = entry_point.seq_front.statements.borrow();
        // 最初の条件式
        assert_eq!(stmts.front(), Some(&cond_stmt));

        // if文の分岐先を確認
        let terminator = entry_point.seq_front.terminator.borrow();
        let Terminator::IfElse { cond, then, otherwise } = &*terminator else {
            panic!("Expected IfElse terminator");
        };
        assert_eq!(*cond, Operand(cond_place));
        // thenブロック
        let then_stmts = then.statements.borrow();
        assert_eq!(then_stmts.front(), Some(&then_expected));
        // elseブロック
        let else_stmts = otherwise.statements.borrow();
        assert_eq!(else_stmts.front(), Some(&else_expected));
    }
}