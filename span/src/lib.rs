use std::{
    fmt::Display,
    ops::{Deref, DerefMut},
};

#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub struct Loc {
    pub line: usize,
    pub col: usize,
}

impl Display for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line {}, col {}", self.line, self.col)
    }
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Span(pub Loc, pub Loc);

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} - {}", self.0, self.1)
    }
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Spanned<T> {
    pub item: T,
    pub span: Span,
}

impl<T: Display> Display for Spanned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} at {}", self.item, self.span)
    }
}

impl<T> Spanned<T> {
    pub fn new(item: T, span: (Loc, Loc)) -> Self {
        Self {
            item,
            span: Span(span.0, span.1),
        }
    }
    pub fn somewhere(item: T) -> Self {
        Self {
            item,
            span: Default::default(),
        }
    }
}

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

impl<T> DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.item
    }
}
