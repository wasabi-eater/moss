use combine::parser::Parser;
use combine::EasyParser;
use typed_arena::Arena;
use crate::infer;
use crate::parser;
use crate::mir_to_cpp;
use crate::mir;
use crate::hir;
use crate::span::{Span, Position};
use crate::ast;
use crate::errors::{Error, SyntaxError, ErrorKind};
use crate::lexer::Lexer;
use crate::token::Token;
use itertools::Itertools;
pub fn compile_to_cpp(source: &str) -> Result<String, Vec<Error>> {
    let tokens = Lexer::new(source).collect_vec();
    let ast_expr = parser::parse_tokens(&tokens, source)?;
    //println!("{:?}", ast_expr);
    let mut hir_maker = hir::Maker::new();
    let hir_expr = hir_maker.from_ast_expr(&ast_expr).map_err(|e| vec![e])?;
    //println!("{:?}", hir_expr);
    let mut infer = infer::Infer::new(infer::Env::new());
    let thir_expr = infer.infer(&hir_expr);
    //println!("{:?}", thir_expr);
    if infer.has_errors() {
        return Err(infer.errors);
    }
    let block_arena = Arena::new();
    let mut mir = mir::Maker::entry_point(thir_expr,&block_arena);
    mir.optimize_memory_operations();
    //println!("{:?}", mir);
    let mut mir_to_cpp_converter = mir_to_cpp::MirToCppConverter::new(mir.stack_env.types.clone());
    let cpp = mir_to_cpp_converter.convert(mir);
    //println!("{}", cpp);
    Ok(cpp)
}
