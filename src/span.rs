use std::cmp;
use std::fmt;
use logos::Span as LogosSpan;

#[derive(Clone, Copy, PartialEq, Eq, Ord)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}

impl Position {
    pub fn new(line: usize, column: usize) -> Self {
        Self { line, column }
    }

    pub fn initial() -> Self {
        Self::new(1, 1)
    }
}
impl cmp::PartialOrd for Position {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        if self.line != other.line {
            Some(self.line.cmp(&other.line))
        } else {
            Some(self.column.cmp(&other.column))
        }
    }
}

impl fmt::Debug for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}
impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: Position,
    pub end: Position,
}
impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}
impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl Span {
    pub fn new(start: Position, end: Position) -> Self {
        Self { start, end }
    }

    pub fn from_logos_span(span: LogosSpan, source: &str) -> Self {
        let before = &source[..span.start];
        let content = &source[span.start..span.end];
        
        let start_line = before.chars().filter(|&c| c == '\n').count() + 1;
        let start_column = before.chars().rev()
            .take_while(|&c| c != '\n')
            .count() + 1;
        
        let end_line = start_line + content.chars().filter(|&c| c == '\n').count();
        let end_column = if content.contains('\n') {
            content.chars().rev()
                .take_while(|&c| c != '\n')
                .count() + 1
        } else {
            start_column + content.chars().count()
        };

        Span {
            start: Position::new(start_line, start_column),
            end: Position::new(end_line, end_column),
        }
    }
    pub fn default() -> Self {
        Self::new(Position::initial(), Position::initial())
    }
    pub fn with_lc(start_line: usize, start_column: usize, end_line: usize, end_column: usize) -> Self {
        Self::new(Position::new(start_line, start_column), Position::new(end_line, end_column))
    }
}

#[derive(Clone, PartialEq)]
pub struct Spanned<T> {
    pub inner: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(inner: T, span: Span) -> Self {
        Self { inner, span }
    }

    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Spanned<U> {
        Spanned {
            inner: f(self.inner),
            span: self.span,
        }
    }
    pub fn as_ref(&self) -> Spanned<&T> {
        Spanned {
            inner: &self.inner,
            span: self.span,
        }
    }
}

impl<T: fmt::Display> fmt::Display for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}
impl<T: fmt::Debug> fmt::Debug for Spanned<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} at {:?}", self.inner, self.span)
    }
}