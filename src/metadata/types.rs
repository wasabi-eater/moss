use std::cell::Cell;
use std::rc::Rc;
use std::fmt;
use itertools::Itertools;

#[derive(PartialEq, Clone, Eq, Hash)]
pub enum Type {
    Primitive(PrimitiveType),
    TypeVar(TypeVar),
    FuncPointer(im::Vector<Type>, Rc<Type>),
    Unknown
}
impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Primitive(p) => write!(f, "{:?}", p),
            Type::TypeVar(v) => write!(f, "{:?}", v),
            Type::FuncPointer(params, ret) => write!(f, "({}) -> {:?}", params.iter().map(|p| format!("{:?}", p)).join(", "), ret),
            Type::Unknown => write!(f, "Unknown"),
        }
    }
}
#[derive(Debug, PartialEq, Clone, Copy, Eq, Hash)]
pub enum PrimitiveType {
    Int,
    Float,
    String,
    Bool,
    Unit,
}
impl Type {
    pub fn free_vars(&self) -> Vec<TypeVar> {
        match self {
            Type::Primitive(_) => vec![],
            Type::TypeVar(var) => vec![*var],
            Type::Unknown => vec![],
            Type::FuncPointer(params, ret) =>
                params.iter().flat_map(|param| param.free_vars()).chain(ret.free_vars()).collect()
        }
    }
    pub fn int() -> Type {
        Type::Primitive(PrimitiveType::Int)
    }
    pub fn string() -> Type {
        Type::Primitive(PrimitiveType::String)
    }
    pub fn float() -> Type {
        Type::Primitive(PrimitiveType::Float)
    }
    pub fn bool() -> Type {
        Type::Primitive(PrimitiveType::Bool)
    }
    pub fn unit() -> Type {
        Type::Primitive(PrimitiveType::Unit)
    }
}

#[derive(Debug, PartialEq, Clone, Copy, Eq, Hash)]
pub struct TypeVar {
    id: usize
}
#[derive(Debug, Clone)]
pub struct VarMaker {
    var_counter: Rc<Cell<usize>>
}
impl VarMaker {
    pub fn new() -> Self {
        Self { var_counter: Rc::new(Cell::new(0)) }
    }
    pub fn new_var(&self) -> TypeVar {
        let id = self.var_counter.get();
        self.var_counter.set(id + 1);
        TypeVar { id }
    }
}
