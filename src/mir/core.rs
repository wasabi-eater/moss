use core::fmt;
use std::cell::RefCell;
use std::hash;
use std::rc::Rc;
use std::collections::{HashMap, HashSet, LinkedList, VecDeque};
use literally::hset;
use crate::metadata::types::Type;
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
            Self::Drop(operand) => vec![operand.clone()],
        }
    }

    pub(crate) fn places(&self) -> Vec<Place> {
        match self {
            Self::Expr(rvalue) => rvalue.places(),
            Self::CopyBinding { from: _, to } => vec![to.clone()],
            Self::MoveBinding { from: _, to } => vec![to.clone()],
            Self::CopyAssign { from: _, to } => vec![to.clone()],
            Self::MoveAssign { from: _, to } => vec![to.clone()],
            Self::Drop(_) => vec![],
        }
    }
}
pub(crate) enum Terminator<'blk> {
    Goto(&'blk SeqBlock<'blk>),
    IfElse { cond: Operand, then: &'blk SeqBlock<'blk>, otherwise: &'blk SeqBlock<'blk> },
    Return(Operand),
}
impl<'blk> fmt::Debug for Terminator<'blk> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Goto(seq) => write!(f, "goto {:?}", seq),
            Self::Return(operand) => write!(f, "return {:?}", operand),
            Self::IfElse { cond, then, otherwise } => write!(f, "if {:?} then {:?} else {:?}", cond, then, otherwise),
        }
    }
}
impl<'blk> Terminator<'blk> {
    pub(crate) fn operands(&self) -> Vec<Operand> {
        match self {
            Self::Goto(_) => vec![],
            Self::Return(operand) => vec![operand.clone()],
            Self::IfElse { cond, then: _, otherwise: _ } => vec![cond.clone()]
        }
    }
    pub(crate) fn shallow_clone(&self) -> Self {
        match self {
            Self::Goto(block) => Self::Goto(*block),
            Self::Return(operand) => Self::Return(operand.clone()),
            Self::IfElse { cond, then, otherwise } =>
                Self::IfElse { cond: cond.clone(), then: *then, otherwise: *otherwise }
        }
    }
}
/// 逐次実行を表現する構造体
/// 
/// 文の列を保持し、プログラムの実行順序を表現します。
pub(crate) struct SeqBlock<'blk> {
    pub(crate) preblocks: RefCell<HashSet<&'blk SeqBlock<'blk>>>,
    pub(crate) statements: RefCell<VecDeque<Statement>>,
    pub(crate) terminator: RefCell<Terminator<'blk>>,
    places_used_later: RefCell<Option<HashSet<Place>>>,
    places_dropped: RefCell<Option<HashSet<Place>>>,
    places_used: HashSet<Place>,
}

impl<'blk> fmt::Debug for SeqBlock<'blk> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for statement in self.statements.borrow().iter() {
            write!(f, "{:?};\n", statement)?;
        }
        write!(f, "{:?}", self.terminator.borrow())?;
        Ok(())
    }
}
impl<'blk> SeqBlock<'blk> {
    pub(crate) fn new(statements: VecDeque<Statement>, terminator: Terminator<'blk>) -> Self {
        let places_used =
            terminator.operands().into_iter()
            .chain(statements.iter().flat_map(|statement| statement.operands()))
            .map(|Operand(place)| place)
            .collect();
        Self {
            preblocks: RefCell::new(hset![]),
            statements: RefCell::new(statements),
            terminator: RefCell::new(terminator),
            places_used_later: RefCell::new(None),
            places_dropped: RefCell::new(None),
            places_used
        }
    }
    pub(crate) fn set_places_used_later(&self, places_used_later: &HashSet<Place>) {
        let new_places_used_later = match self.places_used_later.borrow_mut().as_mut() {
            Some(seq_places_used_later) => {
                let mut new_places_used_later = HashSet::new();
                for &place in places_used_later {
                    if seq_places_used_later.insert(place) {
                        new_places_used_later.insert(place);
                    }
                }
                new_places_used_later
            }
            None => {
                let mut new_places_used_later = HashSet::new();
                new_places_used_later.extend(self.places_used.iter().copied());
                *self.places_used_later.borrow_mut() = Some(new_places_used_later);
                //cloneすることで、self.places_used_laterへの参照を断っている
                //self.places_used_laterへの参照が残っていると、SeqBlockのループがあったときに、borrow_mutができない
                self.places_used_later.borrow().as_ref().unwrap().clone()
            }
        };
        for pre_block in self.preblocks.borrow().iter().copied() {
            pre_block.set_places_used_later(&new_places_used_later);
        }
    }
    //set_places_used_laterの後で呼ばれる必要がある
    pub(crate) fn yield_dropping(&self, places: &HashSet<Place>) {
        if self.places_dropped.borrow().is_none() {
            self.insert_dropping();
        }
        let mut places_dropped = self.places_dropped.borrow_mut();
        let places_dropped = places_dropped.as_mut().unwrap();
        let mut places_newly_dropped = HashSet::new();
        let mut places_dropped_later = HashSet::new();
        for place in places {
            if !places_dropped.insert(*place) { continue; }
            if self.places_used_later.borrow().as_ref().unwrap().contains(&place) {
                places_dropped_later.insert(*place);
            }
            else {
                places_newly_dropped.insert(*place);
            }
        }
        let places_used: HashSet<Place> =
            self.terminator.borrow().operands().into_iter().map(|Operand(place)| place)
            .chain(self.statements.borrow().iter().flat_map(|stmt| stmt.operands().into_iter().map(|Operand(place)| place)))
            .collect();
        let mut statements = self.statements.borrow_mut();
        for place in places_newly_dropped {
            let drop_statement = Statement::Drop(Operand(place));
            if places_used.contains(&place) {
                statements.push_back(drop_statement);
            }
            else {
                statements.push_front(drop_statement);
            }
        }
        match &*self.terminator.borrow() {
            Terminator::Goto(seq) => seq.yield_dropping(&places_dropped_later),
            Terminator::IfElse { cond: _, then, otherwise} => {
                then.yield_dropping(&places_dropped_later);
                otherwise.yield_dropping(&places_dropped_later);
            }
            Terminator::Return(_) => { }
        }
    }
    //set_places_used_laterの後で呼ばれる必要がある
    fn insert_dropping(&self) {
        let mut new_statements = VecDeque::new();
        let mut places_used_later = self.places_used_later.borrow().as_ref().unwrap().clone();
        places_used_later.extend(self.terminator.borrow().operands().into_iter().map(|Operand(place)| place));
        let mut statements = self.statements.borrow_mut();
        let mut places_dropped = HashSet::new();
        while let Some(statement) = statements.pop_back() {
            for place in statement.places() {
                if !places_used_later.contains(&place) {
                    places_dropped.insert(place);
                    new_statements.push_front(Statement::Drop(Operand(place)));
                }
            }
            let places_used = statement.operands().into_iter().map(|Operand(place)| place);
            let statement = match statement {
                Statement::CopyBinding { from: Operand(from), to }
                    if places_used_later.contains(&from) => Statement::MoveBinding { from: Operand(from), to },
                Statement::CopyAssign { from: Operand(from), to }
                    if places_used_later.contains(&from) => Statement::MoveAssign { from: Operand(from), to },
                statement => statement
            };
            new_statements.push_front(statement);
            places_used_later.extend(places_used);
        }
        *statements = new_statements;
        *self.places_dropped.borrow_mut() = Some(places_dropped);
    }
    //selfを含む、selfに繋がっている全てのSeqBlockを返す
    pub fn decendants(&'blk self) -> HashSet<&'blk SeqBlock<'blk>> {
        let mut descendants = HashSet::new();
        let mut queue = LinkedList::new();
        queue.push_back(self);
        while let Some(block) = queue.pop_front() {
            if descendants.insert(block) {
                match &*block.terminator.borrow() {
                    Terminator::Goto(seq) => {
                        queue.push_back(seq);
                    }
                    Terminator::IfElse { cond: _, then, otherwise } => {
                        queue.push_back(then);
                        queue.push_back(otherwise);
                    }
                    Terminator::Return(_) => { }
                }
            }
        }
        descendants
    }
}
//アドレス同士の浅い比較を行う
impl<'blk> PartialEq for &'blk SeqBlock<'blk> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(*self, *other)
    }
}
impl<'blk> Eq for &'blk SeqBlock<'blk> {}
impl<'blk> hash::Hash for &'blk SeqBlock<'blk> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::ptr::hash(*self, state);
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
/// - スタックの情報
/// - 実行される文の列
pub(crate) struct EntryPoint<'blk> {
    pub(crate) stack_env: StackEnv,
    pub(crate) seq_front: &'blk SeqBlock<'blk>,
    pub(crate) seq_backs: Vec<&'blk SeqBlock<'blk>>
}
impl<'blk> EntryPoint<'blk> {
    /// メモリ操作を最適化するメソッド
    /// 
    /// 以下の最適化を行います：
    /// 1. 不要になった変数に対してDrop文を挿入
    /// 2. 最後の使用時のCopy操作をMove操作に変換
    /// 3. 変数の使用回数を追跡し、適切なタイミングでの解放を保証
    pub fn optimize_memory_operations(&mut self) {
        for &back in &self.seq_backs {
            back.set_places_used_later(& HashSet::new());
        }
        let places = self.seq_front.places_used_later.borrow().as_ref().unwrap().clone();
        self.seq_front.yield_dropping(&places);
    }
}
#[derive(Clone, PartialEq, Debug)]
pub(crate) struct StackEnv {
    pub(crate) types: HashMap<Place, Type>,
    pub(crate) is_const: HashMap<Place, bool>,
}

impl<'blk> fmt::Debug for EntryPoint<'blk> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "stack_env: {:?}\n", self.stack_env)?;
        write!(f, "seq: {:?}\n", self.seq_front)?;
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