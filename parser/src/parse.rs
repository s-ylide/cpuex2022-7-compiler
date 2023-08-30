use ast::Expr;
use span::{Loc, Span, Spanned};
use std::fmt::Display;

use crate::lex::{Error as LexError, Lexer, Tok};
use lalrpop_util::lalrpop_mod;
use thiserror::Error;

lalrpop_mod!(pub grammer);

type LalrpopError<'a> = lalrpop_util::ParseError<Loc, Tok<'a>, Spanned<LexError<'a>>>;

#[derive(Debug, Clone, PartialEq, Error)]
pub enum Error<'a> {
    #[error("parse error: unexpected end of file at {0}")]
    Eof(Loc),
    #[error("lex error: {0} at {1}")]
    Lexical(LexError<'a>, Span),
    #[error("parse error: found extra token `{0}` at {1}")]
    ExtraToken(Tok<'a>, Span),
    #[error("parse error: unrecognized token `{0}` at {1}, expected {2}")]
    UnrecognizedToken(Tok<'a>, Span, ExpectedTokens),
}

#[derive(Debug, Clone, PartialEq)]
pub struct ExpectedTokens(Vec<String>);

impl Display for ExpectedTokens {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let v = &self.0;
        match v.len() {
            0 => unreachable!("in this case ExtraToken should be thrown"),
            1 => write!(f, "{}", v[0]),
            _ => write!(f, "one of [{}]", v.join(", ")),
        }
    }
}

fn convert_error(err: LalrpopError) -> Error {
    match err {
        LalrpopError::InvalidToken { location } => Error::Eof(location),
        LalrpopError::ExtraToken {
            token: (lo, tok, hi),
        } => Error::ExtraToken(tok, Span(lo, hi)),
        LalrpopError::User { error } => Error::Lexical(error.item, error.span),
        LalrpopError::UnrecognizedToken {
            token: (lo, tok, hi),
            expected,
        } => Error::UnrecognizedToken(tok, Span(lo, hi), ExpectedTokens(expected)),
        LalrpopError::UnrecognizedEOF { location, .. } => Error::Eof(location),
    }
}

pub fn parse(src: &str) -> Result<Expr, Error> {
    let lex = Lexer::new(src);
    let parser = grammer::ExprParser::new();

    parser.parse(lex).map_err(convert_error)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse() {
        let src = "(* (* x = 3 *) *)
        let (a, a) = ((true + (truw, (), -1) + 1 * 3.5)) in
        (); ()";
        let r = parse(src);
        assert!(r.is_ok(), "{}", r.err().unwrap());
    }

    #[test]
    fn test_parse_minrt() {
        let src = std::fs::read_to_string("./test/minrt.ml").unwrap();
        let r = parse(&src);
        assert!(r.is_ok(), "{}", r.err().unwrap());
    }
}
