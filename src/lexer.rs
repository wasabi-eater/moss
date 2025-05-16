use crate::span::{Span, Spanned};
use crate::token::{Token, TokenKind};
use std::iter::Peekable;

struct LexerCore<'a> {
    logos_lexer: logos::SpannedIter<'a, TokenKind>
}
impl<'a> Iterator for LexerCore<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.logos_lexer.next()?.0.ok()?;
        let span = Span::from_logos_span(self.logos_lexer.span(), self.logos_lexer.source());
        if token != TokenKind::NewLine {
            return Some(Spanned::new(token, span));
        }
        
        Some(Spanned::new(token, span))
    }
}
pub struct Lexer<'a> {
    core: Peekable<LexerCore<'a>>
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            core: LexerCore {
                logos_lexer: logos::Lexer::new(input).spanned(),
            }.peekable(),
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.core.next()?;
        if next.inner != TokenKind::NewLine {
            return Some(next);
        }
        while let Some(token) = self.core.peek() {
            if token.inner != TokenKind::NewLine {
                break;
            }
            _ = self.core.next();
        }
        Some(next)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;
    #[test]
    fn test_basic_tokens() {
        let input = "let x = 42";
        let lexer = Lexer::new(input);
        let tokens: Vec<Token> = lexer.collect();

        assert_eq!(tokens.len(), 4);
        assert_eq!(tokens[0].inner, TokenKind::Let);
        assert_eq!(tokens[1].inner, TokenKind::Identifier(Rc::from("x")));
        assert_eq!(tokens[2].inner, TokenKind::Equal);
        assert_eq!(tokens[3].inner, TokenKind::IntLiteral(Rc::from("42")));
    }

    #[test]
    fn test_operators() {
        let input = "+ - * / & | ^ < > <= >= == != !";
        let lexer = Lexer::new(input);
        let tokens: Vec<Token> = lexer.collect();

        assert_eq!(tokens.len(), 14);
        assert_eq!(tokens[0].inner, TokenKind::Plus);
        assert_eq!(tokens[1].inner, TokenKind::Minus);
        assert_eq!(tokens[2].inner, TokenKind::Asterisk);
        assert_eq!(tokens[3].inner, TokenKind::Slash);
        assert_eq!(tokens[4].inner, TokenKind::Ampersand);
        assert_eq!(tokens[5].inner, TokenKind::Pipe);
        assert_eq!(tokens[6].inner, TokenKind::Caret);
        assert_eq!(tokens[7].inner, TokenKind::Less);
        assert_eq!(tokens[8].inner, TokenKind::Greater);
        assert_eq!(tokens[9].inner, TokenKind::LessEqual);
        assert_eq!(tokens[10].inner, TokenKind::GreaterEqual);
        assert_eq!(tokens[11].inner, TokenKind::Equals);
        assert_eq!(tokens[12].inner, TokenKind::NotEquals);
        assert_eq!(tokens[13].inner, TokenKind::Exclamation);
    }

    #[test]
    fn test_delimiters() {
        let input = "{ } ( ) ;";
        let lexer = Lexer::new(input);
        let tokens: Vec<Token> = lexer.collect();

        assert_eq!(tokens.len(), 5);
        assert_eq!(tokens[0].inner, TokenKind::LeftBrace);
        assert_eq!(tokens[1].inner, TokenKind::RightBrace);
        assert_eq!(tokens[2].inner, TokenKind::LeftParen);
        assert_eq!(tokens[3].inner, TokenKind::RightParen);
        assert_eq!(tokens[4].inner, TokenKind::Semicolon);
    }

    #[test]
    fn test_keywords() {
        let input = "let var true false";
        let lexer = Lexer::new(input);
        let tokens: Vec<Token> = lexer.collect();

        assert_eq!(tokens.len(), 4);
        assert_eq!(tokens[0].inner, TokenKind::Let);
        assert_eq!(tokens[1].inner, TokenKind::Var);
        assert_eq!(tokens[2].inner, TokenKind::BoolLiteral(true));
        assert_eq!(tokens[3].inner, TokenKind::BoolLiteral(false));
    }

    #[test]
    fn test_string_literals() {
        let input = r#""Hello, World!" "Test""#;
        let lexer = Lexer::new(input);
        let tokens: Vec<Token> = lexer.collect();

        assert_eq!(tokens.len(), 2);
        assert_eq!(tokens[0].inner, TokenKind::StringLiteral(Rc::from("Hello, World!")));
        assert_eq!(tokens[1].inner, TokenKind::StringLiteral(Rc::from("Test")));
    }

    #[test]
    fn test_identifiers() {
        let input = "foo bar_baz _test123";
        let lexer = Lexer::new(input);
        let tokens: Vec<Token> = lexer.collect();

        assert_eq!(tokens.len(), 3);
        assert_eq!(tokens[0].inner, TokenKind::Identifier(Rc::from("foo")));
        assert_eq!(tokens[1].inner, TokenKind::Identifier(Rc::from("bar_baz")));
        assert_eq!(tokens[2].inner, TokenKind::Identifier(Rc::from("_test123")));
    }

    #[test]
    fn test_newlines() {
        let input = "let x = 42\n\n\ny = 10";
        let lexer = Lexer::new(input);
        let tokens: Vec<Token> = lexer.collect();

        assert_eq!(tokens.len(), 8);
        assert_eq!(tokens[0].inner, TokenKind::Let);
        assert_eq!(tokens[1].inner, TokenKind::Identifier(Rc::from("x")));
        assert_eq!(tokens[2].inner, TokenKind::Equal);
        assert_eq!(tokens[3].inner, TokenKind::IntLiteral(Rc::from("42")));
        assert_eq!(tokens[4].inner, TokenKind::NewLine);
        assert_eq!(tokens[5].inner, TokenKind::Identifier(Rc::from("y")));
        assert_eq!(tokens[6].inner, TokenKind::Equal);
        assert_eq!(tokens[7].inner, TokenKind::IntLiteral(Rc::from("10")));
    }

    #[test]
    fn test_complex_expression() {
        let input = "let result = (40 + 2) * (3 - 1);";
        let lexer = Lexer::new(input);
        let tokens: Vec<Token> = lexer.collect();

        assert_eq!(tokens.len(), 15);
        assert_eq!(tokens[0].inner, TokenKind::Let);
        assert_eq!(tokens[1].inner, TokenKind::Identifier(Rc::from("result")));
        assert_eq!(tokens[2].inner, TokenKind::Equal);
        assert_eq!(tokens[3].inner, TokenKind::LeftParen);
        assert_eq!(tokens[4].inner, TokenKind::IntLiteral(Rc::from("40")));
        assert_eq!(tokens[5].inner, TokenKind::Plus);
        assert_eq!(tokens[6].inner, TokenKind::IntLiteral(Rc::from("2")));
        assert_eq!(tokens[7].inner, TokenKind::RightParen);
        assert_eq!(tokens[8].inner, TokenKind::Asterisk);
        assert_eq!(tokens[9].inner, TokenKind::LeftParen);
        assert_eq!(tokens[10].inner, TokenKind::IntLiteral(Rc::from("3")));
        assert_eq!(tokens[11].inner, TokenKind::Minus);
        assert_eq!(tokens[12].inner, TokenKind::IntLiteral(Rc::from("1")));
        assert_eq!(tokens[13].inner, TokenKind::RightParen);
        assert_eq!(tokens[14].inner, TokenKind::Semicolon);
    }
} 