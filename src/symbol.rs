use std::borrow::Cow;
use std::rc::Rc;
use std::collections::HashMap;
use std::fmt;

/// コンパイラ全体で使用される一意なシンボルを表現する構造体
#[derive(Clone, Eq)]
pub struct Symbol {
    pub(crate) id: usize,
    pub(crate) name: Rc<str>,
}

impl Symbol {
    pub fn get_id(&self) -> usize {
        self.id
    }

    pub fn name(&self) -> Rc<str> {
        Rc::clone(&self.name)
    }
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl std::hash::Hash for Symbol {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.name)
    }
}
/// シンボルを生成・管理する構造体
#[derive(Debug, Clone)]
pub struct SymbolMaker {
    ids: HashMap<Rc<str>, Symbol>,
    next_id: usize,
}

impl SymbolMaker {
    pub fn new() -> Self {
        SymbolMaker {
            ids: HashMap::new(),
            next_id: 0,
        }
    }

    pub fn symbol<'a>(&mut self, name: impl Into<Rc<str>>) -> Symbol {
        let name = name.into();
        self.ids.get(name.as_ref()).cloned().unwrap_or_else(|| {
            let symbol = Symbol { id: self.next_id, name: Rc::from(name.clone()) };
            self.ids.insert(name, symbol.clone());
            self.next_id += 1;
            symbol
        })
    }
} 