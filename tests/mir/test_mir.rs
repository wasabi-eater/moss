use moss::mir::{EntryPoint, PlaceMaker, Statement, Literal, Rvalue, Operand, BinaryOperator};
use std::collections::HashMap;

#[test]
fn test_optimize_memory_operations() {
    let mut place_maker = PlaceMaker::new();
    let place1 = place_maker.make();
    let place2 = place_maker.make();
    
    let mut entry_point = EntryPoint {
        types: HashMap::new(),
        seq: Default::default(),
        is_const: HashMap::new(),
    };

    // Copy操作を追加
    entry_point.seq.statements.push_back(Statement::Copy {
        from: Operand(place1),
        to: place2,
    });

    // 最適化を実行
    entry_point.optimize_memory_operations();

    // Copy操作がMove操作に変換されていることを確認
    let statement = entry_point.seq.statements.front().unwrap();
    match statement {
        Statement::Move { from: Operand(p1), to: p2 } => {
            assert_eq!(*p1, place1);
            assert_eq!(*p2, place2);
        },
        _ => panic!("Expected Move statement"),
    }
}

#[test]
fn test_literal_operations() {
    let mut place_maker = PlaceMaker::new();
    let place = place_maker.make();
    
    let mut entry_point = EntryPoint {
        types: HashMap::new(),
        seq: Default::default(),
        is_const: HashMap::new(),
    };

    // リテラル操作を追加
    entry_point.seq.statements.push_back(Statement::Expr(
        Rvalue::Literal(place, Literal::Int("42".into()))
    ));

    // 最適化を実行
    entry_point.optimize_memory_operations();

    // Drop文が追加されていることを確認
    assert_eq!(entry_point.seq.statements.len(), 2);
    let last_statement = entry_point.seq.statements.back().unwrap();
    match last_statement {
        Statement::Drop(Operand(p)) => {
            assert_eq!(*p, place);
        },
        _ => panic!("Expected Drop statement"),
    }
}