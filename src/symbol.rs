use std::borrow::Cow;
use std::rc::Rc;
use std::collections::HashMap;
use std::fmt;

/// コンパイラ全体で使用される一意なシンボルを表現する構造体
#[derive(Clone, Eq)]
pub struct Symbol {
    pub(crate) id: usize,
}

impl Symbol {
    pub fn get_id(&self) -> usize {
        self.id
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

/// シンボルを生成・管理する構造体
#[derive(Debug, Clone)]
pub struct SymbolArena {
    names: Vec<Rc<str>>,
    ids: HashMap<Rc<str>, Symbol>,
    next_id: usize,
}

impl SymbolArena {
    pub fn new() -> Self {
        SymbolArena {
            names: Vec::new(),
            ids: HashMap::new(),
            next_id: 0,
        }
    }

    pub fn symbol<'a>(&mut self, name: impl Into<Rc<str>>) -> Symbol {
        let name = name.into();
        self.ids.get(name.as_ref()).cloned().unwrap_or_else(|| {
            let symbol = Symbol { id: self.next_id };
            self.ids.insert(name.clone(), symbol.clone());
            self.names.push(name);
            self.next_id += 1;
            symbol
        })
    }

    pub fn get_name(&self, symbol: &Symbol) -> Option<Rc<str>> {
        if symbol.id < self.names.len() {
            Some(Rc::clone(&self.names[symbol.id]))
        } else {
            None
        }
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Symbol({})", self.id)
    }
} 