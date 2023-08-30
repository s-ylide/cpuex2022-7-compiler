use span::{Loc, Spanned};
use std::{fmt::Display, str::FromStr};

use plex::lexer;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq)]
pub enum Tok<'a> {
    Int(i32),
    Bool(bool),
    Float(f32),
    Ident(&'a str),
    Not,
    Hyphen,
    Plus,
    Ast,
    Slash,
    HyphenDot,
    PlusDot,
    AstDot,
    SlashDot,
    Equal,
    LessGreater,
    LessEqual,
    LessHyphen,
    GreaterEqual,
    Less,
    Greater,
    If,
    Then,
    Else,
    Let,
    In,
    Rec,
    Comma,
    ArrayMake,
    Dot,
    Semi,
    LPar,
    RPar,
}

impl<'a> Display for Tok<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Tok::*;
        match self {
            Int(i) => write!(f, "{i}",),
            Bool(b) => write!(f, "{b}",),
            Float(n) => write!(f, "{n}",),
            Ident(x) => write!(f, "{x}",),
            Not => write!(f, "not"),
            Hyphen => write!(f, "-"),
            Plus => write!(f, "+"),
            Ast => write!(f, "*"),
            Slash => write!(f, "/"),
            HyphenDot => write!(f, "-."),
            PlusDot => write!(f, "+."),
            AstDot => write!(f, "*."),
            SlashDot => write!(f, "/."),
            Equal => write!(f, "="),
            LessGreater => write!(f, "<>"),
            LessEqual => write!(f, "<="),
            LessHyphen => write!(f, "<-"),
            GreaterEqual => write!(f, ">="),
            Less => write!(f, "<"),
            Greater => write!(f, ">"),
            If => write!(f, "if"),
            Then => write!(f, "then"),
            Else => write!(f, "else"),
            Let => write!(f, "let"),
            In => write!(f, "in"),
            Rec => write!(f, "rec"),
            Comma => write!(f, ","),
            ArrayMake => write!(f, "Array.make"),
            Dot => write!(f, "."),
            Semi => write!(f, ";"),
            LPar => write!(f, "("),
            RPar => write!(f, ")"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Error)]
pub enum Error<'a> {
    #[error("reached EOF before comment closes")]
    UnclosedComment,
    #[error("unrecognized token `{0}`")]
    UnrecognizedToken(&'a str),
    #[error("cannot parse `{0}` as integer constant: {1}")]
    IllegalIntegerConstant(&'a str, <i32 as FromStr>::Err),
    #[error("cannot parse `{0}` as float constant: {1}")]
    IllegalFloatConstant(&'a str, <f32 as FromStr>::Err),
}

enum CommentState {
    Open,
    Close,
    Continue,
    NewLine,
}

lexer! {
    fn consume_comment(_text: 'input) -> CommentState;

    r"\(\*" => CommentState::Open,
    r"\*\)" => CommentState::Close,
    r"\n" => CommentState::NewLine,
    r"." => CommentState::Continue
}

enum LexState<'a> {
    Token(Tok<'a>),
    Skip,
    NewLine,
    CommentBegin,
    Error(Error<'a>),
}

lexer! {
    fn next_token(text: 'input) -> LexState<'input>;

    r"\(\*" => LexState::CommentBegin,
    r"[\t\r ]" => LexState::Skip,
    r"\n" => LexState::NewLine,
    r"\(" => LexState::Token(Tok::LPar),
    r"\)" => LexState::Token(Tok::RPar),
    r"true" => LexState::Token(Tok::Bool(true)),
    r"false" => LexState::Token(Tok::Bool(false)),
    r"not" => LexState::Token(Tok::Not),
    r"[0-9]+" => {
        match text.parse() {
            Ok(i) => LexState::Token(Tok::Int(i)),
            Err(e) => LexState::Error(Error::IllegalIntegerConstant(text, e)),
        }
    },
    r"[0-9]+(\.[0-9]*)?([eE][+-]?[0-9]+)?" => {
        match text.parse() {
            Ok(i) => LexState::Token(Tok::Float(i)),
            Err(e) => LexState::Error(Error::IllegalFloatConstant(text, e)),
        }
    },
    r"\-" => LexState::Token(Tok::Hyphen),
    r"\+" => LexState::Token(Tok::Plus),
    r"\*" => LexState::Token(Tok::Ast),
    r"/" => LexState::Token(Tok::Slash),
    r"\-\." => LexState::Token(Tok::HyphenDot),
    r"\+\." => LexState::Token(Tok::PlusDot),
    r"\*\." => LexState::Token(Tok::AstDot),
    r"/\." => LexState::Token(Tok::SlashDot),
    r"=" => LexState::Token(Tok::Equal),
    r"<>" => LexState::Token(Tok::LessGreater),
    r"<=" => LexState::Token(Tok::LessEqual),
    r">=" => LexState::Token(Tok::GreaterEqual),
    r"<" => LexState::Token(Tok::Less),
    r">" => LexState::Token(Tok::Greater),
    r"if" => LexState::Token(Tok::If),
    r"then" => LexState::Token(Tok::Then),
    r"else" => LexState::Token(Tok::Else),
    r"let" => LexState::Token(Tok::Let),
    r"in" => LexState::Token(Tok::In),
    r"rec" => LexState::Token(Tok::Rec),
    r"," => LexState::Token(Tok::Comma),
    r"Array\.make" => LexState::Token(Tok::ArrayMake),
    r"\." => LexState::Token(Tok::Dot),
    r"<\-" => LexState::Token(Tok::LessHyphen),
    r";" => LexState::Token(Tok::Semi),
    r"[a-z_][0-9A-Za-z_]*" => LexState::Token(Tok::Ident(text)),
    r"." => LexState::Error(Error::UnrecognizedToken(text))
}

#[derive(Debug, Clone)]
pub struct Lexer<'input> {
    remain: &'input str,
    last_remain_len: usize,
    current_loc: Loc,
}

impl<'input> Lexer<'input> {
    pub fn new(s: &'input str) -> Self {
        Lexer {
            remain: s,
            last_remain_len: s.chars().count(),
            current_loc: Loc { line: 1, col: 1 },
        }
    }

    fn skip_comment(&mut self) -> std::result::Result<(), Error<'input>> {
        let mut depth = 0;
        loop {
            let state = consume_comment(self.remain);
            if state.is_none() {
                // EOF
                return Err(Error::UnclosedComment);
            }

            let (state, remaining) = state.unwrap();

            self.remain = remaining;
            use CommentState::*;

            match state {
                Open => {
                    depth += 1;
                }
                Close => {
                    if depth == 0 {
                        return Ok(());
                    } else {
                        depth -= 1;
                    }
                }
                NewLine => {
                    self.notice_newline();
                    continue;
                }
                Continue => {
                    const CONCERN: &[char; 4] = &['\n', '(', ')', '*'];
                    self.remain = self
                        .remain
                        .trim_matches(|c| CONCERN.binary_search(&c).is_err());
                    continue;
                }
            }
        }
    }

    fn notice_newline(&mut self) {
        self.current_loc.line += 1;
        self.current_loc.col = 1;
    }
}

type Result<'a> = std::result::Result<(Loc, Tok<'a>, Loc), Spanned<Error<'a>>>;

impl<'input> Iterator for Lexer<'input> {
    type Item = Result<'input>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let state = next_token(self.remain);

            let (state, remaining) = state?;

            self.remain = remaining;

            let remain_len = remaining.chars().count();
            let consumed = self.last_remain_len - remain_len;
            self.last_remain_len = remain_len;

            let lo = self.current_loc;
            self.current_loc.col += consumed;
            let hi = self.current_loc;

            use LexState::*;

            match state {
                Token(tok) => return Some(Ok((lo, tok, hi))),
                Skip => continue,
                NewLine => {
                    self.notice_newline();
                    continue;
                }
                Error(e) => return Some(Err(Spanned::new(e, (lo, hi)))),
                CommentBegin => {
                    if let Err(e) = self.skip_comment() {
                        return Some(Err(Spanned::new(e, (lo, hi))));
                    }
                }
            }
        }
    }
}
