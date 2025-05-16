# ![recursion_limit = "256"]

pub mod ast;
pub mod compiler;
pub mod errors;
pub mod hir;
pub mod infer;
pub mod mir;
pub mod mir_to_cpp;
pub mod parser;
pub mod span;
pub mod symbol;
pub mod thir;
pub mod types;
pub mod lexer;
pub mod token;
pub use crate::compiler::compile_to_cpp;