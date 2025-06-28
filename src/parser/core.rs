use combine::{attempt, choice, eof, many, many1, optional, satisfy, sep_end_by, unexpected, value, Parser};
use combine::parser;
use crate::ast::{Expression, ExpressionKind, connect_spans};
use crate::span::{Spanned, Position, Span};
use crate::token::{Token, TokenKind};
use std::rc::Rc;
trait Stream: combine::Stream<Token = Token, Position = combine::stream::PointerOffset<[Token]>> {
    
}
impl <S: combine::stream::Stream<Token = Token, Position = combine::stream::PointerOffset<[Token]>>> Stream for S {
    
}

parser! {
    fn map_spanned[Input, T, U, P, F](parser: P, f: F)(Input) -> Spanned<U>
    where [Input: Stream, P: Parser<Input, Output = Spanned<T>>, F: FnMut(T) -> U]
    {
        parser.map(|spanned| spanned.map(|inner| f(inner)))
    }
}
trait MapParserSpannedExt<Input: Stream, T>: Parser<Input, Output = Spanned<T>> {
    fn map_spanned<U, F>(self, f: F) -> map_spanned<Input, T, U, Self, F>
    where
        Self: Sized,
        F: FnMut(T) -> U,
    {
        map_spanned(self, f)
    }
}
impl<Input: Stream, T, P: Parser<Input, Output = Spanned<T>>> MapParserSpannedExt<Input, T> for P { }

parser! {
    fn any_token[Input]()(Input) -> Token
    where [Input: Stream]
    {
        satisfy(|_| true)
    }
}
parser! {
    fn token[Input](kind: TokenKind)(Input) -> Token
    where [Input: Stream] {
        attempt(satisfy(move |token: Token| token.inner == kind.clone()))
    }
}
parser! {
    fn token_fn[Input, T, F](getter: F)(Input) -> T
    where [Input: Stream, T: Clone, F: FnMut(Token) -> Result<T, Token>] {
        attempt(any_token().then(|token: Token| {
            match getter(token) {
                Ok(result) => value(result).right(),
                Err(token) => unexpected(combine::error::Token(token)).map(|_| unreachable!()).left(),
            }
        }))
    }
}

// Identifier parser
parser! {
    fn identifier[Input]()(Input) -> Spanned<Rc<str>>
    where [Input: Stream]
    {
        token_fn(Token::identifier)
    }
}

parser! {
    fn assignment[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (
            identifier(),
            token(TokenKind::Equal),
            expression(),
        )
        .map(|(name,  _, value)| {
            let span = connect_spans(name.span, value.span);
            Spanned::new(ExpressionKind::assignment(name, value), span)
        })
    }
}

// Integer parser
parser! {
    fn int[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        token_fn(Token::int_literal).map_spanned(ExpressionKind::int)
    }
}

// Float parser
parser! {
    fn float[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        token_fn(Token::float_literal).map_spanned(ExpressionKind::float)
    }
}
// Boolean parser
parser! {
    fn boolean[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        token_fn(Token::bool_literal).map_spanned(ExpressionKind::boolean)
    }
}

// String literal parser
parser! {
    fn string_literal[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        token_fn(Token::string_literal).map_spanned(ExpressionKind::string_literal)
    }
}

parser! {
    fn if_expr[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (
            token(TokenKind::If).skip(token(TokenKind::NewLine)),
            expression().skip(token(TokenKind::NewLine)),
            block().map_spanned(ExpressionKind::block),
            many(attempt((
                optional(token(TokenKind::NewLine)),
                token(TokenKind::Else).skip(token(TokenKind::NewLine)),
                token(TokenKind::If).skip(token(TokenKind::NewLine)),
                expression().skip(token(TokenKind::NewLine)),
                block().map_spanned(ExpressionKind::block),
            ))),
            optional(attempt((
                optional(token(TokenKind::NewLine)),
                token(TokenKind::Else).skip(token(TokenKind::NewLine)),
                block().map_spanned(ExpressionKind::block),
            ))),
        )
        .map(|(if_token, cond, then, else_ifs, else_):
            (Token, Expression, Expression,
                Vec<(Option<Token>, Token, Token, Expression, Expression)>,
                Option<(Option<Token>, Token, Expression)>)| {
            let else_ = else_.map(|(_, _, expr)| expr);
            let else_ =
                else_ifs.into_iter().rev()
                .fold(else_, |acc, (_, else_token, _, cond, then)| {
                    let span = connect_spans(else_token.span, acc.as_ref().map(|acc| acc.span).unwrap_or(then.span));
                    Some(Spanned::new(ExpressionKind::if_(cond, then, acc), span))
                });
           let span = connect_spans(if_token.span, else_.as_ref().map(|else_| else_.span).unwrap_or(then.span));
           Spanned::new(ExpressionKind::if_(cond, then, else_), span)
        })
    }
}

// Term parser
parser! {
    fn term[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        choice((
            boolean(),
            int(),
            float(),
            identifier().map_spanned(ExpressionKind::variable),
            string_literal(),
            block().map_spanned(ExpressionKind::block),
            parentheses(),
            if_expr(),
        ))
    }
}
parser! {
    fn postfix_operator[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (term(), many(choice((token(TokenKind::Question), token(TokenKind::Exclamation)))))
            .map(|(expr, ops): (Expression, Vec<Token>)|
                ops.into_iter().fold(expr, |acc, op| {
                    let span = connect_spans(acc.span, op.span);
                    Spanned::new(
                        ExpressionKind::postfix_unary_operation(acc, Spanned::new(format!("{}", op.inner), op.span)),
                        span
                    )
                }))
    }
}
parser! {
    fn prefix_operator[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (many(choice((token(TokenKind::Minus), token(TokenKind::Exclamation)))), postfix_operator())
            .map(|(ops, expr): (Vec<Token>, Expression)|
                ops.into_iter().rev().fold(expr, |acc, op| {
                    let span = connect_spans(op.span, acc.span);
                    Spanned::new(
                        ExpressionKind::prefix_unary_operation(Spanned::new(format!("{}", op.inner), op.span), acc),
                        span
                    )
                }))
    }
}
parser! {
    fn mul_binary_operator[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (prefix_operator(), many((
            choice((token(TokenKind::Asterisk), token(TokenKind::Slash))),
            prefix_operator()
        ))).map(|(left, op_right_pairs): (Expression, Vec<(Token, Expression)>)| 
            op_right_pairs.into_iter().fold(left, |acc, (op, right)| {
                let span = connect_spans(acc.span, right.span);
                Spanned::new(ExpressionKind::binary_operation(acc, Spanned::new(format!("{}", op.inner), op.span), right), span)
            }))
    }
}

parser! {
    fn plus_binary_operator[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (mul_binary_operator(), many((
            choice((token(TokenKind::Plus), token(TokenKind::Minus))),
            mul_binary_operator()
        ))).map(|(left, op_right_pairs): (Expression, Vec<(Token, Expression)>)| 
        op_right_pairs.into_iter().fold(left, |acc, (op, right)| {
            let span = connect_spans(acc.span, right.span);
            Spanned::new(ExpressionKind::binary_operation(acc, Spanned::new(format!("{}", op.inner), op.span), right), span)
        }))
    }
}
parser! {
    fn and_binary_operator[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (plus_binary_operator(), many((
            token(TokenKind::Ampersand),
            plus_binary_operator()
        ))).map(|(left, op_right_pairs): (Expression, Vec<(Token, Expression)>)| 
        op_right_pairs.into_iter().fold(left, |acc, (op, right)| {
            let span = connect_spans(acc.span, right.span);
            Spanned::new(ExpressionKind::binary_operation(acc, Spanned::new(format!("{}", op.inner), op.span), right), span)
        }))
    }
}
parser! {
    fn xor_binary_operator[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (and_binary_operator(), many((
            token(TokenKind::Caret),
            and_binary_operator()
        ))).map(|(left, op_right_pairs): (Expression, Vec<(Token, Expression)>)| 
        op_right_pairs.into_iter().fold(left, |acc, (op, right)| {
            let span = connect_spans(acc.span, right.span);
            Spanned::new(ExpressionKind::binary_operation(acc, Spanned::new("^".to_string(), op.span), right), span)
        }))
    }
}
parser! {
    fn or_binary_operator[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (xor_binary_operator(), many((
            token(TokenKind::Pipe),
            xor_binary_operator()
        ))).map(|(left, op_right_pairs): (Expression, Vec<(Token, Expression)>)| 
        op_right_pairs.into_iter().fold(left, |acc, (op, right)| {
            let span = connect_spans(acc.span, right.span);
            Spanned::new(ExpressionKind::binary_operation(acc, Spanned::new("|".to_string(), op.span), right), span)
        }))
    }
}
parser! {
    fn comparison_operator[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (
            or_binary_operator(),
            optional(attempt((
                choice((token(TokenKind::LessEqual), token(TokenKind::GreaterEqual), token(TokenKind::Less), token(TokenKind::Greater))),
                or_binary_operator()
            )))
        ).map(|(left, rem)| {
            let Some((op, right)) = rem else { return left };
            let span = connect_spans(left.span, right.span);
            Spanned::new(ExpressionKind::binary_operation(left, Spanned::new(format!("{}", op.inner), op.span), right), span)
        })
    }
}
parser! {
    fn equality_operator[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (
            comparison_operator(),
            optional(attempt((
                choice((token(TokenKind::Equals), token(TokenKind::NotEquals))),
                comparison_operator()
            )))
        ).map(|(left, rem)| {
            match rem {
                Some((op, right)) => {
                    let span = connect_spans(left.span, right.span);
                    Spanned::new(ExpressionKind::binary_operation(left, Spanned::new(format!("{}", op.inner), op.span), right), span)
                }
                None => left
            }
        })
    }
}
    

// Expression parser
parser! {
    fn expression[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        equality_operator()
    }
}
parser! {
    fn declare_var[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (
            choice((token(TokenKind::Let), token(TokenKind::Var))),
            identifier(),
            token(TokenKind::Equal),
            expression(),
        )
        .map(|(declare, name, _, value)| {
            let span = connect_spans(declare.span, name.span);
            Spanned::new(
                if declare.inner == TokenKind::Let {
                    ExpressionKind::let_(name, value)
                }
                else {
                    ExpressionKind::var(name, value)
                },
                span
            )
        })
    }
}

// Statement parser
parser! {
    fn statement[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        choice((
            attempt(declare_var()),
            attempt(assignment()),
            attempt(expression())
        ))
    }
}
// Line separator parser
parser! {
    fn statement_separator[Input]()(Input) -> ()
    where [Input: Stream]
    {
        many1(new_line().or(token(TokenKind::Semicolon).map(|_| ())))
    }
}
parser! {
    fn new_line[Input]()(Input) -> ()
    where [Input: Stream]
    {
        token(TokenKind::NewLine).map(|_| ())
    }
}

parser! {
    fn statements[Input]()(Input) -> Vec<Expression>
    where [Input: Stream]
    {
        (optional(attempt(statement_separator())), sep_end_by(statement(), statement_separator()))
            .map(|(_, statements)| statements)
    }
}

parser! {
    fn block[Input]()(Input) -> Spanned<Vec<Expression>>
    where [Input: Stream]
    {
        (
            token(TokenKind::LeftBrace),
            statements(),
            token(TokenKind::RightBrace),
        )
        .map(|(left, block, right)| {
            let span = connect_spans(left.span, right.span);
            Spanned::new(block, span)
        })
    }
}

parser! {
    fn parentheses[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (
            token(TokenKind::LeftParen),
            expression(),
            token(TokenKind::RightParen),
        )
        .map(|(_, expr, _)| expr)
    }
}

// Program parser
parser! {
    pub(crate) fn program[Input]()(Input) -> Expression
    where [Input: Stream]
    {
        (statements(), eof()).map(|(statements, _)| {
            let start_pos = Position { line: 1, column: 1 };
            let last_pos = statements.last().map(|last| last.span.end).unwrap_or(start_pos);
            Spanned::new(ExpressionKind::block(statements), Span::new(start_pos, last_pos))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use combine::{easy, EasyParser};
    //型推論しやすくする為に、型を指定している
    fn expr<'a>() -> impl Parser<easy::Stream<&'a [Token]>, Output = Expression> {
        expression()
    }
    fn statement<'a>() -> impl Parser<easy::Stream<&'a [Token]>, Output = Expression> {
        super::statement()
    }
    fn statements<'a>() -> impl Parser<easy::Stream<&'a [Token]>, Output = Vec<Expression>> {
        super::statements()
    }
    fn block<'a>() -> impl Parser<easy::Stream<&'a [Token]>, Output = Spanned<Vec<Expression>>> {
        super::block()
    }
    #[test]
    fn test_int_literal() {
        //42
        let tokens = vec![Token::new(TokenKind::IntLiteral(Rc::from("42")), Span::with_lc(1, 1, 1, 3))];
        let result = expr().easy_parse(tokens.as_ref());
        assert_eq!(result, Ok((Spanned::new(ExpressionKind::int(Rc::from("42")), Span::with_lc(1, 1, 1, 3)), [].as_ref())));
    }
    #[test]
    fn test_float_literal() {
        //42.0
        let tokens = vec![Token::new(TokenKind::FloatLiteral(Rc::from("42.0")), Span::with_lc(1, 1, 1, 5))];
        let result = expr().easy_parse(tokens.as_ref());
        assert_eq!(result, Ok((Spanned::new(ExpressionKind::float(Rc::from("42.0")), Span::with_lc(1, 1, 1, 5)), [].as_ref())));
    }

    #[test]
    fn test_binary_expression() {
        //1 + 2 * 3
        let tokens: Vec<Token> = vec![
            Token::new(TokenKind::IntLiteral(Rc::from("1")), Span::with_lc(1, 1, 1, 2)),
            Token::new(TokenKind::Plus, Span::with_lc(1, 2, 1, 3)),
            Token::new(TokenKind::IntLiteral(Rc::from("2")), Span::with_lc(1, 3, 1, 4)),
            Token::new(TokenKind::Asterisk, Span::with_lc(1, 4, 1, 5)),
            Token::new(TokenKind::IntLiteral(Rc::from("3")), Span::with_lc(1, 5, 1, 6)),
        ];
        let result = expr().easy_parse(tokens.as_ref());    
        let ExpressionKind::BinaryOperation (ref left, ref operator, ref right) =
            result.unwrap().0.inner else { panic!("Expected binary operation") };
        assert_eq!(left.inner, ExpressionKind::int(Rc::from("1")));
        assert_eq!(operator.inner, "+");
        let ExpressionKind::BinaryOperation (ref left, ref operator, ref right) =
            right.inner else { panic!("Expected binary operation") };
        assert_eq!(left.inner, ExpressionKind::int(Rc::from("2")));
        assert_eq!(operator.inner, "*");
        assert_eq!(right.inner, ExpressionKind::int(Rc::from("3")));
    }

    #[test]
    fn test_variable_declaration() {
        //let x = 42
        let tokens = vec![
            Token::new(TokenKind::Let, Span::with_lc(1, 1, 1, 4)),
            Token::new(TokenKind::Identifier(Rc::from("x")), Span::with_lc(1, 5, 1, 6)),
            Token::new(TokenKind::Equal, Span::with_lc(1, 6, 1, 7)),
            Token::new(TokenKind::IntLiteral(Rc::from("42")), Span::with_lc(1, 7, 1, 9)),
        ];
        let result = statement().easy_parse(tokens.as_ref());
        let ExpressionKind::Let (ref name, ref value) =
            result.unwrap().0.inner else { panic!("Expected let expression") };
        assert_eq!(name.inner.as_ref(), "x");
        assert_eq!(value.inner, ExpressionKind::int(Rc::from("42")));
    }
    #[test]
    fn test_block_expression() {
        //{let x = 1; x + 2}
        let tokens = vec![
            Token::new(TokenKind::LeftBrace, Span::with_lc(1, 1, 1, 2)),
            Token::new(TokenKind::Let, Span::with_lc(1, 2, 1, 5)),
            Token::new(TokenKind::Identifier(Rc::from("x")), Span::with_lc(1, 6, 1, 7)),
            Token::new(TokenKind::Equal, Span::with_lc(1, 7, 1, 8)),
            Token::new(TokenKind::IntLiteral(Rc::from("1")), Span::with_lc(1, 8, 1, 9)),
            Token::new(TokenKind::Semicolon, Span::with_lc(1, 9, 1, 10)),
            Token::new(TokenKind::Identifier(Rc::from("x")), Span::with_lc(1, 11, 1, 12)),
            Token::new(TokenKind::Plus, Span::with_lc(1, 12, 1, 13)),
            Token::new(TokenKind::IntLiteral(Rc::from("2")), Span::with_lc(1, 13, 1, 14)),
            Token::new(TokenKind::RightBrace, Span::with_lc(1, 14, 1, 15)),
        ];
        let result = expr().easy_parse(tokens.as_ref());
        let ExpressionKind::Block(ref statements) =
            result.unwrap().0.inner else { panic!("Expected block expression") };
        assert_eq!(statements.len(), 2);
        let ExpressionKind::Let (ref name, ref value) =
            statements[0].inner else { panic!("Expected let expression") };
        assert_eq!(name.inner.as_ref(), "x");
        assert_eq!(value.inner, ExpressionKind::int("1"));
        let ExpressionKind::BinaryOperation (ref left, ref operator, ref right) =
            statements[1].inner else { panic!("Expected binary operation") };
        assert_eq!(left.inner, ExpressionKind::variable("x"));
        assert_eq!(operator.inner, "+");
        assert_eq!(right.inner, ExpressionKind::int("2"));
    }


    #[test]
    fn test_comparison_operators() {
        let operators = vec![TokenKind::Less, TokenKind::Greater, TokenKind::LessEqual, TokenKind::GreaterEqual];
        for op in operators {
            let tokens = vec![
                Token::new(TokenKind::Identifier(Rc::from("x")), Span::with_lc(1, 1, 1, 2)),
                Token::new(op.clone(), Span::with_lc(1, 2, 1, 3)),
                Token::new(TokenKind::IntLiteral(Rc::from("42")), Span::with_lc(1, 3, 1, 5)),
            ];
            let result = expr().easy_parse(tokens.as_ref());
            let ExpressionKind::BinaryOperation (ref left, ref operator, ref right) =
                result.unwrap().0.inner else { panic!("Expected binary operation") };
            assert_eq!(left.inner, ExpressionKind::variable("x"));
            assert_eq!(operator.inner, op.to_string());
            assert_eq!(right.inner, ExpressionKind::int("42"));
        }
    }

    #[test]
    fn test_equality_operators() {
        let operators = vec![TokenKind::Equals, TokenKind::NotEquals];
        for op in operators {
            let tokens = vec![
                Token::new(TokenKind::Identifier(Rc::from("x")), Span::with_lc(1, 1, 1, 2)),
                Token::new(op.clone(), Span::with_lc(1, 2, 1, 3)),
                Token::new(TokenKind::IntLiteral(Rc::from("42")), Span::with_lc(1, 3, 1, 5)),
            ];
            let result = expr().easy_parse(tokens.as_ref());
            let ExpressionKind::BinaryOperation (ref left, ref operator, ref right) =
                result.unwrap().0.inner else { panic!("Expected binary operation") };
            assert_eq!(left.inner, ExpressionKind::variable("x"));
            assert_eq!(operator.inner, op.to_string());
            assert_eq!(right.inner, ExpressionKind::int("42"));
        }
    }

    #[test]
    fn test_statements() {
        // let x = 1; let y = 2
        let tokens = vec![
            Token::new(TokenKind::Let, Span::with_lc(1, 1, 1, 4)),
            Token::new(TokenKind::Identifier(Rc::from("x")), Span::with_lc(1, 5, 1, 6)),
            Token::new(TokenKind::Equal, Span::with_lc(1, 7, 1, 8)),
            Token::new(TokenKind::IntLiteral(Rc::from("1")), Span::with_lc(1, 9, 1, 10)),
            Token::new(TokenKind::Semicolon, Span::with_lc(1, 10, 1, 11)),
            Token::new(TokenKind::Let, Span::with_lc(1, 12, 1, 15)),
            Token::new(TokenKind::Identifier(Rc::from("y")), Span::with_lc(1, 16, 1, 17)),
            Token::new(TokenKind::Equal, Span::with_lc(1, 18, 1, 19)),
            Token::new(TokenKind::IntLiteral(Rc::from("2")), Span::with_lc(1, 20, 1, 21)),
        ];
        let result = statements().easy_parse(tokens.as_ref());
        let (stmts, _) = result.unwrap();
        assert_eq!(stmts.len(), 2);

        let ExpressionKind::Let(ref name1, ref value1) = stmts[0].inner else {
            panic!("Expected let expression");
        };
        assert_eq!(name1.inner.as_ref(), "x");
        assert_eq!(value1.inner, ExpressionKind::int("1"));

        let ExpressionKind::Let(ref name2, ref value2) = stmts[1].inner else {
            panic!("Expected let expression");
        };
        assert_eq!(name2.inner.as_ref(), "y");
        assert_eq!(value2.inner, ExpressionKind::int("2"));
    }

    #[test]
    fn test_statements_with_newlines() {
        // let x = 1\nlet y = 2
        let tokens = vec![
            Token::new(TokenKind::Let, Span::with_lc(1, 1, 1, 4)),
            Token::new(TokenKind::Identifier(Rc::from("x")), Span::with_lc(1, 5, 1, 6)),
            Token::new(TokenKind::Equal, Span::with_lc(1, 7, 1, 8)),
            Token::new(TokenKind::IntLiteral(Rc::from("1")), Span::with_lc(1, 9, 1, 10)),
            Token::new(TokenKind::NewLine, Span::with_lc(1, 10, 2, 1)),
            Token::new(TokenKind::Let, Span::with_lc(2, 1, 2, 4)),
            Token::new(TokenKind::Identifier(Rc::from("y")), Span::with_lc(2, 5, 2, 6)),
            Token::new(TokenKind::Equal, Span::with_lc(2, 7, 2, 8)),
            Token::new(TokenKind::IntLiteral(Rc::from("2")), Span::with_lc(2, 9, 2, 10)),
        ];
        let result = statements().easy_parse(tokens.as_ref());
        let (stmts, _) = result.unwrap();
        assert_eq!(stmts.len(), 2);
    }

    #[test]
    fn test_empty_block() {
        // {}
        let tokens = vec![
            Token::new(TokenKind::LeftBrace, Span::with_lc(1, 1, 1, 2)),
            Token::new(TokenKind::RightBrace, Span::with_lc(1, 2, 1, 3)),
        ];
        let result = block().easy_parse(tokens.as_ref());
        let (block_expr, _) = result.unwrap();
        assert_eq!(block_expr.inner.len(), 0);
    }

    #[test]
    fn test_nested_blocks() {
        // { let x = { 1 }; }
        let tokens = vec![
            Token::new(TokenKind::LeftBrace, Span::with_lc(1, 1, 1, 2)),
            Token::new(TokenKind::Let, Span::with_lc(1, 3, 1, 6)),
            Token::new(TokenKind::Identifier(Rc::from("x")), Span::with_lc(1, 7, 1, 8)),
            Token::new(TokenKind::Equal, Span::with_lc(1, 9, 1, 10)),
            Token::new(TokenKind::LeftBrace, Span::with_lc(1, 11, 1, 12)),
            Token::new(TokenKind::IntLiteral(Rc::from("1")), Span::with_lc(1, 13, 1, 14)),
            Token::new(TokenKind::RightBrace, Span::with_lc(1, 15, 1, 16)),
            Token::new(TokenKind::Semicolon, Span::with_lc(1, 16, 1, 17)),
            Token::new(TokenKind::RightBrace, Span::with_lc(1, 18, 1, 19)),
        ];
        let result = block().easy_parse(tokens.as_ref());
        let (block_expr, _) = result.unwrap();
        assert_eq!(block_expr.inner.len(), 1);

        let ExpressionKind::Let(ref name, ref value) = block_expr.inner[0].inner else {
            panic!("Expected let expression");
        };
        assert_eq!(name.inner.as_ref(), "x");

        let ExpressionKind::Block(ref inner_block) = value.inner else {
            panic!("Expected block expression");
        };
        assert_eq!(inner_block.len(), 1);
        let ExpressionKind::Int(ref num) = inner_block[0].inner else {
            panic!("Expected integer literal");
        };
        assert_eq!(num.as_ref(), "1");
    }

    #[test]
    fn test_if_expression_simple() {
        // if x { 1 }
        let tokens = vec![
            Token::new(TokenKind::If, Span::with_lc(1, 1, 1, 3)),
            Token::new(TokenKind::NewLine, Span::with_lc(1, 3, 2, 1)),
            Token::new(TokenKind::Identifier(Rc::from("x")), Span::with_lc(2, 1, 2, 2)),
            Token::new(TokenKind::NewLine, Span::with_lc(2, 2, 3, 1)),
            Token::new(TokenKind::LeftBrace, Span::with_lc(3, 1, 3, 2)),
            Token::new(TokenKind::IntLiteral(Rc::from("1")), Span::with_lc(3, 2, 3, 3)),
            Token::new(TokenKind::RightBrace, Span::with_lc(3, 3, 3, 4)),
        ];
        let result = expr().easy_parse(tokens.as_ref());
        let ExpressionKind::If(cond, then, else_) = &result.unwrap().0.inner else {
            panic!("Expected if expression");
        };
        assert_eq!(cond.inner, ExpressionKind::variable("x"));
        let ExpressionKind::Block(ref stmts) = then.inner else {
            panic!("Expected block in then");
        };
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0].inner, ExpressionKind::int("1"));
        assert!(else_.is_none());
    }

    #[test]
    fn test_if_else_expression() {
        // if x { 1 } else { 2 }
        let tokens = vec![
            Token::new(TokenKind::If, Span::with_lc(1, 1, 1, 3)),
            Token::new(TokenKind::NewLine, Span::with_lc(1, 3, 2, 1)),
            Token::new(TokenKind::Identifier(Rc::from("x")), Span::with_lc(2, 1, 2, 2)),
            Token::new(TokenKind::NewLine, Span::with_lc(2, 2, 3, 1)),
            Token::new(TokenKind::LeftBrace, Span::with_lc(3, 1, 3, 2)),
            Token::new(TokenKind::IntLiteral(Rc::from("1")), Span::with_lc(3, 2, 3, 3)),
            Token::new(TokenKind::RightBrace, Span::with_lc(3, 3, 3, 4)),
            Token::new(TokenKind::Else, Span::with_lc(3, 5, 3, 9)),
            Token::new(TokenKind::NewLine, Span::with_lc(3, 9, 4, 1)),
            Token::new(TokenKind::LeftBrace, Span::with_lc(4, 1, 4, 2)),
            Token::new(TokenKind::IntLiteral(Rc::from("2")), Span::with_lc(4, 2, 4, 3)),
            Token::new(TokenKind::RightBrace, Span::with_lc(4, 3, 4, 4)),
        ];
        let result = expr().easy_parse(tokens.as_ref());
        let ExpressionKind::If(cond, then, else_) = &result.unwrap().0.inner else {
            panic!("Expected if expression");
        };
        assert_eq!(cond.inner, ExpressionKind::variable("x"));
        let ExpressionKind::Block(ref stmts) = then.inner else {
            panic!("Expected block in then");
        };
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0].inner, ExpressionKind::int("1"));
        let Some(else_expr) = else_ else { panic!("Expected else branch"); };
        let ExpressionKind::Block(ref stmts) = else_expr.inner else {
            panic!("Expected block in else");
        };
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0].inner, ExpressionKind::int("2"));
    }

    #[test]
    fn test_if_elseif_else_expression() {
        // if x { 1 } else if y { 2 } else { 3 }
        let tokens = vec![
            Token::new(TokenKind::If, Span::with_lc(1, 1, 1, 3)),
            Token::new(TokenKind::NewLine, Span::with_lc(1, 3, 2, 1)),
            Token::new(TokenKind::Identifier(Rc::from("x")), Span::with_lc(2, 1, 2, 2)),
            Token::new(TokenKind::NewLine, Span::with_lc(2, 2, 3, 1)),
            Token::new(TokenKind::LeftBrace, Span::with_lc(3, 1, 3, 2)),
            Token::new(TokenKind::IntLiteral(Rc::from("1")), Span::with_lc(3, 2, 3, 3)),
            Token::new(TokenKind::RightBrace, Span::with_lc(3, 3, 3, 4)),
            Token::new(TokenKind::Else, Span::with_lc(3, 5, 3, 9)),
            Token::new(TokenKind::NewLine, Span::with_lc(3, 9, 4, 1)),
            Token::new(TokenKind::If, Span::with_lc(4, 1, 4, 3)),
            Token::new(TokenKind::NewLine, Span::with_lc(4, 3, 5, 1)),
            Token::new(TokenKind::Identifier(Rc::from("y")), Span::with_lc(5, 1, 5, 2)),
            Token::new(TokenKind::NewLine, Span::with_lc(5, 2, 6, 1)),
            Token::new(TokenKind::LeftBrace, Span::with_lc(6, 1, 6, 2)),
            Token::new(TokenKind::IntLiteral(Rc::from("2")), Span::with_lc(6, 2, 6, 3)),
            Token::new(TokenKind::RightBrace, Span::with_lc(6, 3, 6, 4)),
            Token::new(TokenKind::Else, Span::with_lc(6, 5, 6, 9)),
            Token::new(TokenKind::NewLine, Span::with_lc(6, 9, 7, 1)),
            Token::new(TokenKind::LeftBrace, Span::with_lc(7, 1, 7, 2)),
            Token::new(TokenKind::IntLiteral(Rc::from("3")), Span::with_lc(7, 2, 7, 3)),
            Token::new(TokenKind::RightBrace, Span::with_lc(7, 3, 7, 4)),
        ];
        let result = expr().easy_parse(tokens.as_ref());
        let ExpressionKind::If(cond, then, else_) = &result.unwrap().0.inner else {
            panic!("Expected if expression");
        };
        assert_eq!(cond.inner, ExpressionKind::variable("x"));
        let ExpressionKind::Block(ref stmts) = then.inner else {
            panic!("Expected block in then");
        };
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0].inner, ExpressionKind::int("1"));

        let Some(else_expr) = else_ else { panic!("Expected else branch"); };
        let ExpressionKind::If(cond, then, else_) = &else_expr.inner else {
            panic!("Expected else-if expression");
        };
        assert_eq!(cond.inner, ExpressionKind::variable("y"));
        let ExpressionKind::Block(ref stmts) = then.inner else {
            panic!("Expected block in else-if then");
        };
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0].inner, ExpressionKind::int("2"));

        let Some(else_expr2) = else_ else { panic!("Expected else branch after else-if"); };
        let ExpressionKind::Block(ref stmts) = else_expr2.inner else {
            panic!("Expected block in else after else-if");
        };
        assert_eq!(stmts.len(), 1);
        assert_eq!(stmts[0].inner, ExpressionKind::int("3"));
    }
}