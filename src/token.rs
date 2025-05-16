use std::fmt;
use logos::Logos;
use crate::span::Spanned;
use std::rc::Rc;

#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(skip r"[ \t\f\r]+")]  // 水平タブ、フォームフィード、キャリッジリターンを無視
#[logos(skip r"\x{2000}-\x{200F}")]  // Unicodeの様々な空白文字を無視
#[logos(skip r"\x{2028}")]  // Line Separator
#[logos(skip r"\x{202F}")]  // Narrow No-Break Space
#[logos(skip r"\x{205F}")]  // Medium Mathematical Space
#[logos(skip r"\x{3000}")]  // 全角スペース
pub enum TokenKind {
    // 改行の特別処理
    #[regex(r"[\n]*\n[ \t\f\r]*", |_| ())]
    NewLine,

    // キーワード
    #[token("let")]
    Let,
    
    #[token("var")]
    Var,
    
    #[token("true", |_| true)]
    #[token("false", |_| false)]
    BoolLiteral(bool),

    // リテラル
    #[regex(r"([\p{XID_Start}]|_)[\p{XID_Continue}]*", |lex| Rc::from(lex.slice()))]
    Identifier(Rc<str>),
    
    #[regex(r"\d+", |lex| Rc::from(lex.slice()))]
    IntLiteral(Rc<str>),
    
    #[regex(r"\d+\.\d+", |lex| Rc::from(lex.slice()))]
    FloatLiteral(Rc<str>),
    
    #[regex(r#""[^"]*""#, |lex| {
        let slice = lex.slice();
        Rc::from(&slice[1..slice.len()-1])
    })]
    StringLiteral(Rc<str>),

    // 演算子
    #[token("+")]
    Plus,
    
    #[token("-")]
    Minus,
    
    #[token("*")]
    Asterisk,
    
    #[token("/")]
    Slash,
    
    #[token("==")]
    Equals,
    
    #[token("!=")]
    NotEquals,
    
    // 区切り文字
    #[token("(")]
    LeftParen,
    
    #[token(")")]
    RightParen,
    
    #[token("{")]
    LeftBrace,
    
    #[token("}")]
    RightBrace,
    
    #[token(";")]
    Semicolon,

    #[token("&")]
    Ampersand,

    #[token("|")]
    Pipe,

    #[token("^")]
    Caret,

    #[token("!")]
    Exclamation,

    #[token("?")]
    Question,

    #[token("=")]
    Equal,

    #[token("<")]
    Less,

    #[token(">")]
    Greater,

    #[token("<=")]
    LessEqual,

    #[token(">=")]
    GreaterEqual,
}

pub type Token = Spanned<TokenKind>;

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Identifier(name) => write!(f, "{}", name),
            TokenKind::IntLiteral(value) => write!(f, "{}", value),
            TokenKind::FloatLiteral(value) => write!(f, "{}", value),
            TokenKind::StringLiteral(value) => write!(f, "\"{}\"", value),
            TokenKind::BoolLiteral(value) => write!(f, "{}", value),
            TokenKind::Let => write!(f, "let"),
            TokenKind::Var => write!(f, "var"),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Asterisk => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::Equals => write!(f, "=="),
            TokenKind::NotEquals => write!(f, "!="),
            TokenKind::Ampersand => write!(f, "&"),
            TokenKind::Pipe => write!(f, "|"),
            TokenKind::Caret => write!(f, "^"),
            TokenKind::Exclamation => write!(f, "!"),
            TokenKind::Question => write!(f, "?"),
            TokenKind::LeftParen => write!(f, "("),
            TokenKind::RightParen => write!(f, ")"),
            TokenKind::LeftBrace => write!(f, "{{"),
            TokenKind::RightBrace => write!(f, "}}"),
            TokenKind::Semicolon => write!(f, ";"),
            TokenKind::Equal => write!(f, "="),
            TokenKind::Less => write!(f, "<"),
            TokenKind::Greater => write!(f, ">"),
            TokenKind::LessEqual => write!(f, "<="),
            TokenKind::GreaterEqual => write!(f, ">="),
            TokenKind::NewLine => write!(f, "\n"),
        }
    }
}
impl Token {
    pub fn identifier(self) -> Result<Spanned<Rc<str>>, Token> { 
        match self.inner {
            TokenKind::Identifier(name) => Ok(Spanned::new(name, self.span)),
            _ => Err(self),
        }
    }
    pub fn int_literal(self) -> Result<Spanned<Rc<str>>, Token> { 
        match self.inner {
            TokenKind::IntLiteral(value) => Ok(Spanned::new(value, self.span)),
            _ => Err(self),
        }
    }
    pub fn float_literal(self) -> Result<Spanned<Rc<str>>, Token> { 
        match self.inner {
            TokenKind::FloatLiteral(value) => Ok(Spanned::new(value, self.span)),
            _ => Err(self),
        }
    }
    pub fn string_literal(self) -> Result<Spanned<Rc<str>>, Token> { 
        match self.inner {
            TokenKind::StringLiteral(value) => Ok(Spanned::new(value, self.span)),
            _ => Err(self),
        }
    }
    pub fn bool_literal(self) -> Result<Spanned<bool>, Token> { 
        match self.inner {
            TokenKind::BoolLiteral(value) => Ok(Spanned::new(value, self.span)),
            _ => Err(self),
        }
    }
}