mod core;

use crate::ast::Expression;
use crate::parser::core::program;
use crate::token::Token;
use crate::errors::{Error, ErrorKind, SyntaxError};
use crate::span::{Span, Position};
use combine::EasyParser;
pub fn parse_tokens(tokens: &[Token], source: &str) -> Result<Expression, Vec<Error>> {
    let result = program().easy_parse(tokens);
    match result {
        Ok((expr, _)) => Ok(expr),
        Err(err) => {
            let mut expected = vec![];
            let mut unexpected = vec![];
            let mut message = vec![];
            for error in err.errors { 
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
            let position = err.position.translate_position(&tokens);
            let line = source[..position].lines().count() + 1;
            let column = source[..position].lines().nth_back(0).unwrap_or(source).len() + 1;
            Err(vec![Error {
                span: Span { start: Position { line, column }, end: Position { line, column } },
                    kind: ErrorKind::SyntaxError(SyntaxError {
                        unexpected,
                        expected,
                        message,
                    }),
                }])
        }
    }
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