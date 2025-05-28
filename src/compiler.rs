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
fn program<'a>() -> impl Parser<combine::easy::Stream<&'a [Token]>, Output = ast::Expression> {
    parser::program()
}
fn info_to_string(info: combine::easy::Info<Token, &[Token]>) -> String {
    match info {
        combine::easy::Info::Range(range) => {
            format!("{:?}", range)
        }
        combine::easy::Info::Owned(message) => {
            format!("{}", message)
        }
        combine::easy::Info::Static(message) => {
            format!("{}", message)
        }
        combine::easy::Info::Token(info) => {
            format!("{:?}", info)
        }
    }
}
pub fn compile_to_cpp(source: &str) -> Result<String, Vec<Error>> {
    let lexer = Lexer::new(source).collect_vec();
    //println!("{:?}", lexer);
    let result = program().easy_parse(lexer.as_ref());
    let (ast_expr, _) = result.map_err(|e|{
        let mut expected = vec![];
        let mut unexpected = vec![];
        let mut message = vec![];
        for error in e.errors { 
            match error {
                combine::easy::Error::Unexpected(info) => {
                    unexpected.push(info_to_string(info));
                }
                combine::easy::Error::Expected(info) => {
                    expected.push(info_to_string(info));
                }
                combine::easy::Error::Message(info) => {
                    message.push(info_to_string(info));
                }
                combine::easy::Error::Other(_) => { }
            }
        }
        let position = e.position.translate_position(&lexer);
        let line = source[..position].lines().count() + 1;
        let column = source[..position].lines().nth_back(0).unwrap_or(source).len() + 1;
        vec![Error {
            span: Span { start: Position { line, column }, end: Position { line, column } },
                kind: ErrorKind::SyntaxError(SyntaxError {
                    unexpected,
                    expected,
                    message,
                }),
            }]
    })?;
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
