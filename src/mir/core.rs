use core::fmt;
use std::rc::Rc;
use std::collections::{HashMap, LinkedList};

use crate::types::Type;

/// リテラル値を表現する列挙型
///
#[derive(Clone, PartialEq)]
pub(crate) enum Literal {
    Int(Rc<str>),
    Float(Rc<str>),
    String(Rc<str>),
    Bool(bool),
    Unit
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Bool(b) => write!(f, "{b}"),
            Literal::Float(n) => write!(f, "{n}"),
            Literal::String(s) => write!(f, "{s}"),
            Literal::Int(i) => write!(f, "{i}"),
            Literal::Unit => write!(f, "()"),
        }
    }
}

/// 右辺値（Rvalue）を表現する列挙型
/// 
/// 計算や代入の右辺に現れる式を表現します。
/// 二項演算、単項演算、リテラルの3種類の式をサポートしています。
#[derive(Clone, PartialEq)]
pub(crate) enum Rvalue {
    BinaryOp(Place, Operand, BinaryOperator, Operand),
    UnaryOperator(Place, UnaryOperator, Operand),
    Literal(Place, Literal)
}

impl Rvalue {
    pub(crate) fn operands(&self) -> Vec<Operand> {
        match self {
            Self::BinaryOp(_, left, _, right) => vec![left.clone(), right.clone()],
            Self::Literal(_, _) => vec![],
            Self::UnaryOperator(_, _, operand) => vec![operand.clone()]
        }
    }

    pub(crate) fn places(&self) -> Vec<Place> {
        match self {
            Self::BinaryOp(place, _, _, _) => vec![place.clone()],
            Self::Literal(place, _) => vec![place.clone()],
            Self::UnaryOperator(place, _, _) => vec![place.clone()]
        }
    }
}
impl fmt::Debug for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BinaryOp(place, left, op, right) => write!(f, "{:?} = ({:?} {:?} {:?})", place, left, op, right),
            Self::Literal(place, literal) => write!(f, "{:?} = {:?}", place, literal),
            Self::UnaryOperator(place, op, operand) => write!(f, "{:?} = ({:?} {:?})", place, op, operand),
        }
    }
}

/// オペランドを表現する構造体
/// 
/// 式の中で使用される値への参照を表現します。
#[derive(Debug, PartialEq, Clone)]
pub(crate) struct Operand(pub Place);

/// メモリ上の位置を表す構造体
/// 
/// 変数やテンポラリの格納位置を一意に識別します。
/// `id`フィールドは位置を一意に特定するために使用されます。
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub(crate) struct Place {
    pub(crate) id: usize
}
impl fmt::Debug for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "${}", self.id)
    }
}

/// MIRにおける文（Statement）を表現する列挙型
/// 
/// プログラムの各ステップを表現します。以下の種類の文をサポートします：
/// - 式の評価（Expr）
/// - メモリの解放（Drop）
/// - 値のコピーして束縛（CopyBinding）
/// - 値の移動して束縛（MoveBinding）
/// - 値のコピーして代入（CopyAssign）
/// - 値の移動して代入（MoveAssign）
#[derive(Clone, PartialEq)]
pub(crate) enum Statement {
    Expr(Rvalue),
    Drop(Operand),
    CopyBinding { from: Operand, to: Place },
    MoveBinding { from: Operand, to: Place },
    CopyAssign { from: Operand, to: Place },
    MoveAssign { from: Operand, to: Place },
}
impl fmt::Debug for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expr(rvalue) => write!(f, "{:?}", rvalue),
            Self::Drop(operand) => write!(f, "drop {:?}", operand),
            Self::CopyBinding { from, to } => write!(f, "{:?} := {:?}", to, from),
            Self::MoveBinding { from, to } => write!(f, "{:?} := move {:?}", to, from),
            Self::CopyAssign { from, to } => write!(f, "{:?} <- {:?}", to, from),
            Self::MoveAssign { from, to } => write!(f, "{:?} <- move {:?}", to, from),
        }
    }
}

impl Statement {
    pub(crate) fn operands(&self) -> Vec<Operand> {
        match self {
            Self::Expr(rvalue) => rvalue.operands(),
            Self::CopyBinding { from, to: _ } => vec![from.clone()],
            Self::MoveBinding { from, to: _ } => vec![from.clone()],
            Self::CopyAssign { from, to: _ } => vec![from.clone()],
            Self::MoveAssign { from, to: _ } => vec![from.clone()],
            Self::Drop(operand) => vec![operand.clone()]
        }
    }

    pub(crate) fn places(&self) -> Vec<Place> {
        match self {
            Self::Expr(rvalue) => rvalue.places(),
            Self::CopyBinding { from: _, to } => vec![to.clone()],
            Self::MoveBinding { from: _, to } => vec![to.clone()],
            Self::CopyAssign { from: _, to } => vec![to.clone()],
            Self::MoveAssign { from: _, to } => vec![to.clone()],
            Self::Drop(_) => vec![]
        }
    }
}

/// 逐次実行を表現する構造体
/// 
/// 文の列を保持し、プログラムの実行順序を表現します。
#[derive(Clone, PartialEq)]
pub(crate) struct SequentialExecution {
    pub(crate) statements: LinkedList<Statement>
}
impl fmt::Debug for SequentialExecution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for statement in self.statements.iter() {
            write!(f, "{:?};\n", statement)?;
        }
        Ok(())
    }
}

/// 二項演算子を表現する列挙型
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub(crate) enum BinaryOperator {
    Add(Type, Type),
    Subtract(Type, Type),
    Multiply(Type, Type),
    Divide(Type, Type),
    Equal(Type, Type),
    NotEqual(Type, Type),
    LessThan(Type, Type),
    LessThanOrEqual(Type, Type),
    GreaterThan(Type, Type),
    GreaterThanOrEqual(Type, Type),
    And(Type, Type),
    Or(Type, Type),
    Xor(Type, Type),
}

/// 単項演算子を表現する列挙型
#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub(crate) enum UnaryOperator {
    Minus(Type),
    Not(Type),
}

/// プログラムのエントリーポイントを表現する構造体
/// 
/// 以下の情報を保持します：
/// - 各メモリ位置の型情報
/// - 実行される文の列
/// - 定数値の情報
#[derive(Clone, PartialEq)]
pub(crate) struct EntryPoint {
    pub(crate) types: HashMap<Place, Type>,
    pub(crate) seq: SequentialExecution,
    pub(crate) is_const: HashMap<Place, bool>
}

impl EntryPoint {
    /// メモリ操作を最適化するメソッド
    /// 
    /// 以下の最適化を行います：
    /// 1. 不要になった変数に対してDrop文を挿入
    /// 2. 最後の使用時のCopy操作をMove操作に変換
    /// 3. 変数の使用回数を追跡し、適切なタイミングでの解放を保証
    pub fn optimize_memory_operations(&mut self) {
        let mut place_read_counts: HashMap<Place, usize> = HashMap::new();
        let mut new_statements = LinkedList::new();
        while let Some(statement) = self.seq.statements.pop_back() {
            let places = statement.places();
            for place in places {
                if place_read_counts.get(&place).copied().unwrap_or(0) == 0 {
                    new_statements.push_front(Statement::Drop(Operand(place)));
                }
            }
            let operands = statement.operands();
            new_statements.push_front(match statement {
                Statement::CopyBinding { from: Operand(from), to }
                    if place_read_counts.get(&from).copied().unwrap_or(0) == 0 =>
                    Statement::MoveBinding { from: Operand(from), to },
                Statement::CopyAssign { from: Operand(from), to }
                    if place_read_counts.get(&from).copied().unwrap_or(0) == 0 =>
                    Statement::MoveAssign { from: Operand(from), to },
                statement => statement
            });
            for Operand(place) in operands {
                *place_read_counts.entry(place).or_insert(0) += 1;
            }
        }
        self.seq.statements = new_statements;
    }
}
impl fmt::Debug for EntryPoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "types: {:?}\n", self.types)?;
        write!(f, "is_const: {:?}\n", self.is_const)?;
        write!(f, "seq: {:?}\n", self.seq)?;
        Ok(())
    }
}

/// メモリ位置（Place）を生成するためのユーティリティ構造体
/// 
/// 一意なIDを持つPlace構造体を順次生成します。
pub(crate) struct PlaceMaker {
    counter: usize
}

impl PlaceMaker {
    pub fn new() -> Self {
        Self { counter: 0 }
    }

    pub fn make(&mut self) -> Place {
        self.counter += 1;
        Place { id: self.counter - 1 }
    }
}