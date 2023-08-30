use std::{
    fs::File,
    io::{BufReader, Read, Write},
    process::ExitCode,
};

use annotate_snippets::{
    display_list::{DisplayList, FormatOptions},
    snippet::{Annotation, AnnotationType, Slice, Snippet, SourceAnnotation},
};
use clap::Parser;
use debug_symbol::DebugSymbol;
use ir_asm_parser_isa1st::{AdditionalInfo, Diagnosis};
use thiserror::Error;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// File path to output debug symbol
    #[arg(short, long)]
    dbg: Option<String>,
    /// File path to input
    #[arg(short, long)]
    input: String,
    /// File path to output
    #[arg(short, long)]
    output: Option<String>,
    /// Output 32-bit integers(LE) in each line instead of binary
    #[arg(short, long)]
    ascii: bool,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error("{0}")]
    ParseError(String),
    #[error(transparent)]
    SerError(#[from] serde_json::Error),
}

fn main() -> ExitCode {
    env_logger::init();
    let r = assembler();
    if let Err(e) = r {
        eprintln!("{e}");
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}

fn assembler() -> Result<(), Error> {
    let Args {
        dbg,
        input: path,
        output,
        ascii,
    } = Args::parse();
    let mut file = File::open(&path)?;
    let mut input = String::new();
    file.read_to_string(&mut input)?;
    let asm = ir_asm_parser_isa1st::parse(&input).map_err(
        |ir_asm_parser_isa1st::Error { line_number, inner }| {
            let source = input
                .lines()
                .nth(line_number - 1)
                .unwrap_or_else(|| panic!("invalid line_number: `{line_number}` for {path}"));
            let source: String = source
                .chars()
                .map(|c| match c {
                    '\t' => ' ',
                    c => c,
                })
                .collect();
            let label = format!("{inner}");

            let Diagnosis {
                range,
                label: l,
                level: _,
                info,
            } = inner.diagnosis();
            let ann = SourceAnnotation {
                range,
                label: &l,
                annotation_type: AnnotationType::Error,
            };
            let outlive;

            let snippet = Snippet {
                title: Some(Annotation {
                    label: Some(&label),
                    id: None,
                    annotation_type: AnnotationType::Error,
                }),
                footer: vec![],
                slices: {
                    let s2 = Slice {
                        source: &source,
                        line_start: line_number,
                        origin: Some(&path),
                        fold: true,
                        annotations: vec![ann],
                    };
                    match info {
                        Some(AdditionalInfo { line, range, label }) => {
                            outlive = label;
                            let s1 = Slice {
                                source: &source,
                                line_start: line,
                                origin: Some(&path),
                                annotations: vec![SourceAnnotation {
                                    range,
                                    label: &outlive,
                                    annotation_type: AnnotationType::Info,
                                }],
                                fold: true,
                            };
                            vec![s1, s2]
                        }
                        None => vec![s2],
                    }
                },
                opt: FormatOptions {
                    color: true,
                    ..Default::default()
                },
            };

            let dl = DisplayList::from(snippet);
            Error::ParseError(dl.to_string())
        },
    )?;
    let mut debug_symbol: DebugSymbol = Default::default();
    let bytes = bingen_isa1st::assemble_and_link(asm, None, &mut debug_symbol);
    let mut file = File::create(output.unwrap_or_else(|| "a.out".to_string()))?;
    if ascii {
        let mut reader = BufReader::new(bytes.as_slice());
        loop {
            let mut buf = [0; 4];
            let n = reader.read(&mut buf)?;
            if n == 0 {
                break;
            }
            writeln!(&mut file, "{:08X}", u32::from_le_bytes(buf))?;
        }
    } else {
        file.write_all(bytes.as_slice())?;
    }
    if let Some(dbg) = dbg {
        let mut file = File::create(dbg)?;
        let s = serde_json::to_string(&debug_symbol)?;
        file.write_all(s.as_bytes())?;
    }

    Ok(())
}
