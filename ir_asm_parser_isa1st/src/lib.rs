use ir_asm_ast_isa1st::{
    Asm, DataSegment, StaticLibrary, TextSegment, TextSegmentDirective, TextSegmentElem,
};
use parser::{SectionKind, Span, Spanned, VerifyError};
use thiserror::Error;
use typedefs::{Ident, Label};

mod parser;

pub struct Diagnosis {
    pub range: (usize, usize),
    pub label: String,
    pub level: DiagnosisLevel,
    pub info: Option<AdditionalInfo>,
}

pub struct AdditionalInfo {
    pub line: usize,
    pub range: (usize, usize),
    pub label: String,
}

impl Diagnosis {
    pub fn new(range: (usize, usize), label: String) -> Self {
        Self {
            range,
            label,
            level: DiagnosisLevel::Error,
            info: None,
        }
    }
    pub fn info(mut self, info: AdditionalInfo) -> Self {
        self.info = Some(info);
        self
    }
}

pub enum DiagnosisLevel {
    Error,
}

#[derive(Debug, PartialEq, Error)]
pub enum ErrorKind<'input> {
    #[error("failed to parse assembly file")]
    PegError(#[from] peg::error::ParseError<peg::str::LineCol>),
    #[error("duplicate entry of {second_occur} section")]
    DupSection {
        second_occur: parser::SectionBegin,
        previous: (usize, parser::Span),
    },
    #[error("invalid {} in {1} section", .0.kind())]
    InvalidLineInSection(parser::Line<'input>, parser::SectionKind),
    #[error("invalid {} before beginning of section", .0.kind())]
    InvalidLineBeforeSectionBegins(parser::Line<'input>),
    #[error("{0}")]
    VerifyError(VerifyError<'input>),
    #[error("program should contain at least one .text section")]
    NoTextSection,
}

impl<'input> ErrorKind<'input> {
    pub fn diagnosis(&self) -> Diagnosis {
        match self {
            ErrorKind::PegError(peg::error::ParseError { location, expected }) => {
                let loc = location.offset;
                Diagnosis::new((loc, loc + 1), format!("expected {expected}"))
            }
            ErrorKind::DupSection {
                second_occur,
                previous,
            } => {
                let section = second_occur.inner.clone();
                let span2 = second_occur.span;
                let (line, span) = *previous;
                Diagnosis::new(span2, format!("second occurrence of {section}")).info(
                    AdditionalInfo {
                        line,
                        range: span,
                        label: format!("first occurrence of {section}"),
                    },
                )
            }
            ErrorKind::InvalidLineInSection(Spanned { span, inner }, s) => {
                Diagnosis::new(*span, format!("invalid {} in {s}", inner.kind()))
            }
            ErrorKind::InvalidLineBeforeSectionBegins(Spanned { span, inner }) => Diagnosis::new(
                *span,
                format!("{} should not come before section begins", inner.kind()),
            ),
            ErrorKind::VerifyError(e) => match e {
                VerifyError::MismatchArgs {
                    at: _,
                    expect,
                    actual,
                } => Diagnosis::new(actual.span, format!("expected {expect}")),
                VerifyError::MismatchArgsCount {
                    line_span,
                    expect_len,
                    actual_len,
                } => Diagnosis::new(
                    *line_span,
                    format!("expected {expect_len}, actual {actual_len}"),
                ),
                VerifyError::UnsupportedInstr { name } => {
                    Diagnosis::new(name.span, format!("unknown instruction `{name}`"))
                }
                VerifyError::InvalidRegName { actual } => {
                    Diagnosis::new(actual.span, format!("invalid register name `{actual}`"))
                }
            },
            ErrorKind::NoTextSection => Diagnosis::new(
                (0, 0),
                "unexpected end of file before reach .text".to_string(),
            ),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Error<'input> {
    pub line_number: usize,
    pub inner: ErrorKind<'input>,
}

impl<'a> ErrorKind<'a> {
    #[inline]
    fn at(self, line_number: usize) -> Error<'a> {
        Error {
            line_number,
            inner: self,
        }
    }
}

struct SingleSectionBuilder<T> {
    section: SectionKind,
    acc: Option<Vec<T>>,
    begin: Option<(usize, Span)>,
}

impl<T> SingleSectionBuilder<T> {
    #[inline]
    fn new(section: SectionKind) -> Self {
        Self {
            section,
            acc: None,
            begin: None,
        }
    }
    #[inline]
    fn entry<'a>(self, line_number: usize, span: Span) -> Result<'a, Self> {
        if self.begin.is_some() {
            return Err(ErrorKind::DupSection {
                second_occur: (Spanned::new(span, self.section)),
                previous: self.begin.unwrap(),
            }
            .at(line_number));
        }
        Ok(Self {
            section: self.section,
            acc: Some(Vec::new()),
            begin: Some((line_number, span)),
        })
    }
    #[inline]
    fn push(&mut self, data: T) {
        self.acc.as_mut().unwrap().push(data);
    }
    #[inline]
    fn inner(self) -> Option<Vec<T>> {
        self.acc
    }
}

type Result<'input, T> = ::std::result::Result<T, Error<'input>>;

pub fn parse(input: &str) -> Result<Asm<Ident, Label>> {
    let (data_segment, text_segment) = parse_input(input)?;
    Ok(Asm {
        data_segment,
        text_segment,
        entry_point: Label::raw_name("main"),
    })
}

pub fn parse_library(input: &str) -> Result<StaticLibrary<Label>> {
    let (data_segment, text_segment) = parse_input(input)?;
    assert!(
        data_segment.is_empty(),
        "currently .data in lib doesn't get supported"
    );
    Ok(StaticLibrary { text_segment })
}

fn parse_input(input: &str) -> Result<(DataSegment<Ident, Label>, TextSegment<Label>)> {
    use parser::*;
    let mut text_segment = SingleSectionBuilder::new(SectionKind::Text);
    let mut data_segment = SingleSectionBuilder::new(SectionKind::Data);
    let mut current_section_kind = None;
    for (input, line_number) in input.lines().zip(1..) {
        let line = parser::asm::line(input).map_err(|e| ErrorKind::PegError(e).at(line_number))?;
        if let Some(line) = line {
            use DirectiveCall::*;
            use LineKind::*;
            use SectionKind::*;
            match (line.inner, &current_section_kind) {
                (SectionBegin(s), _) => {
                    match s {
                        Text => {
                            text_segment = text_segment.entry(line_number, line.span)?;
                        }
                        Data => {
                            data_segment = data_segment.entry(line_number, line.span)?;
                        }
                    };
                    current_section_kind = Some(s);
                }
                (Directive(Skip), _) => {
                    log::warn!("skipped directive.")
                }
                (Instr(i), Some(Text)) => {
                    let i = verify_instr_call(line.span, i)
                        .map_err(|e| ErrorKind::VerifyError(e).at(line_number))?;
                    text_segment.push(TextSegmentElem::Text(i));
                }
                (LabelDef(l), Some(Text)) => {
                    text_segment.push(TextSegmentElem::Directive(TextSegmentDirective::Labeled(
                        Label::raw_name(*l),
                    )));
                }
                (inner, Some(c)) => Err(ErrorKind::InvalidLineInSection(
                    Spanned {
                        span: line.span,
                        inner,
                    },
                    c.clone(),
                )
                .at(line_number))?,
                (inner, None) => Err(ErrorKind::InvalidLineBeforeSectionBegins(Spanned {
                    span: line.span,
                    inner,
                })
                .at(line_number))?,
            }
        }
    }
    Ok((
        DataSegment::new(data_segment.inner().unwrap_or_default()),
        text_segment
            .inner()
            .ok_or_else(|| ErrorKind::NoTextSection.at(input.lines().count()))
            .map(TextSegment::new)?,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse() {
        parse(
            r#"
    .text
main:
    nop
        "#,
        )
        .unwrap();
    }
}
