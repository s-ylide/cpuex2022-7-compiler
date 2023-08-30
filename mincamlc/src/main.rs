use std::{
    fs::File,
    io::{Read, Write},
};

use clap::{Args, Parser, Subcommand};
use debug_symbol::DebugSymbol;
use ir_asm_virtual_isa1st::{CollectUsage, VirtualAsm};
use pervasives::ASM_LIBS;
use thiserror::Error;
use typing::TypeckError;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// compiles
    Compile(CompileArgument),
    /// generate assembly
    Asm(Argument),
    /// generate virtual assembly
    VAsm(Argument),
}

#[derive(Args, Debug)]
struct CompileArgument {
    /// File path to output debug symbol
    #[arg(short, long)]
    dbg: Option<String>,
    #[command(flatten)]
    delegate: Argument,
}

#[derive(Args, Debug)]
struct Argument {
    /// File path to input
    #[arg(short, long)]
    input: Vec<String>,
    /// File path to output
    #[arg(short, long)]
    output: Option<String>,
    /// output path to knorm (optional)
    #[arg(short, long)]
    knorm: Option<String>,
}

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error("{0}")]
    ParseError(String),
    #[error("{0}")]
    TypeError(TypeckError),
    #[error(transparent)]
    SerError(#[from] serde_json::Error),
}

fn main() -> Result<(), Error> {
    env_logger::init();
    let args = Cli::parse();
    match args.command {
        Commands::Compile(CompileArgument {
            dbg,
            delegate:
                Argument {
                    input,
                    output,
                    knorm,
                },
        }) => {
            let mut debug_symbol: DebugSymbol = Default::default();
            let src = input_src(input)?;
            let (virtasm, st) = generate_virtasm(&src, knorm)?;
            let asm = ir_asm_virtual_isa1st::asm_transform(virtasm, st);
            let exe = ir_asm_virtual_isa1st::exe_transform(asm);
            let asm =
                bingen_isa1st::assemble_and_link(exe, Some(ASM_LIBS.clone()), &mut debug_symbol);
            let mut file = File::create(output.unwrap_or_else(|| "a.out".to_string()))?;
            file.write_all(asm.as_slice())?;
            if let Some(dbg) = dbg {
                let mut file = File::create(dbg)?;
                let s = serde_json::to_string(&debug_symbol)?;
                file.write_all(s.as_bytes())?;
            }
        }
        Commands::Asm(Argument {
            input,
            output,
            knorm,
        }) => {
            let src = input_src(input)?;
            let (virtasm, c) = generate_virtasm(&src, knorm)?;
            let asm = ir_asm_virtual_isa1st::asm_transform(virtasm, c);
            let exe = ir_asm_virtual_isa1st::exe_transform(asm);
            let mut file = File::create(output.unwrap_or_else(|| "a.out".to_string()))?;
            write!(file, "{exe}")?;
        }
        Commands::VAsm(Argument {
            input,
            output,
            knorm,
        }) => {
            let src = input_src(input)?;
            let (virtasm, _) = generate_virtasm(&src, knorm)?;
            let mut file = File::create(output.unwrap_or_else(|| "a.out".to_string()))?;
            write!(file, "{virtasm}")?;
        }
    }
    Ok(())
}

/// input files from path, all files combined into one String in the specified order
fn input_src(input: Vec<String>) -> Result<String, Error> {
    let mut src = include_str!("../../pervasives/src/ast/floats.ml").to_string();
    for path in input {
        let mut file = File::open(path)?;
        file.read_to_string(&mut src)?;
    }
    Ok(src)
}

fn generate_virtasm(
    src: &str,
    knorm_path: Option<String>,
) -> Result<(VirtualAsm, CollectUsage), Error> {
    let mut parsed = parser::parse(src).map_err(|e| Error::ParseError(format!("{e}")))?;
    typing::typeck(&mut parsed).map_err(Error::TypeError)?;
    ir_typed_ast::shortcut_fusion(&mut parsed);
    ir_typed_ast::recognize_primitive(&mut parsed);
    let mut knorm = ir_knorm::knorm_transform(parsed);
    ir_knorm::alpha_convert(&mut knorm);
    ir_knorm::destruct_tuple(&mut knorm);
    let mut st = ir_knorm::PathState::default();
    loop {
        ir_knorm::beta_convert(&mut knorm, &mut st);
        ir_knorm::inlining(&mut knorm, &mut st);
        ir_knorm::flatten_let(&mut knorm, &mut st);
        ir_knorm::find_static_alias(&knorm, &mut st);
        ir_knorm::const_folding(&mut knorm, &mut st);
        ir_knorm::find_unused_let(&knorm, &mut st);
        ir_knorm::elim_unused(&mut knorm, &mut st);
        if !st.modified() {
            break;
        } else {
            st.clear_modified();
        }
    }
    #[cfg(feature = "create_loop")]
    {
        ir_knorm::create_loop(&mut knorm, &mut st);
        loop {
            ir_knorm::beta_convert(&mut knorm, &mut st);
            ir_knorm::inlining(&mut knorm, &mut st);
            ir_knorm::flatten_let(&mut knorm, &mut st);
            ir_knorm::find_static_alias(&knorm, &mut st);
            ir_knorm::const_folding(&mut knorm, &mut st);
            ir_knorm::elim_common_expr(&mut knorm, &mut st);
            ir_knorm::find_unused_let(&knorm, &mut st);
            ir_knorm::elim_unused(&mut knorm, &mut st);
            if !st.modified() {
                break;
            } else {
                st.clear_modified();
            }
        }
    }
    if let Some(p) = knorm_path {
        write!(File::create(p)?, "{knorm}")?;
    }
    let mut closure = ir_closure::closure_transform(knorm);
    ir_closure::inlining_arg(&mut closure);
    let mut virtasm = ir_asm_virtual_isa1st::asmv_transform(closure);

    let mut st = ir_asm_virtual_isa1st::PathState::default();
    use ir_asm_virtual_isa1st::Collectable;
    for fundef in virtasm.fundefs.iter_mut() {
        ir_asm_virtual_isa1st::tail_call(fundef);
        #[cfg(feature = "remove_unused_store")]
        ir_asm_virtual_isa1st::remove_unused_store(fundef, &mut st);
        ir_asm_virtual_isa1st::redundant_param(fundef, &mut st);
        #[cfg(feature = "isa_2nd")]
        ir_asm_virtual_isa1st::restore_branch_imm(fundef);
        loop {
            ir_asm_virtual_isa1st::copy_propagation(fundef, &mut st);
            st.usage_of_var.clear();
            fundef.collect_usage(&mut st.usage_of_var);
            ir_asm_virtual_isa1st::remove_unused_def(fundef, &mut st);
            ir_asm_virtual_isa1st::remove_unlinked_bb(fundef);
            ir_asm_virtual_isa1st::rec_coalesce_jumps(fundef, &mut st);
            if !st.modified() {
                break;
            } else {
                st.clear_modified();
            }
        }
        ir_asm_virtual_isa1st::remove_unlinked_bb(fundef);
        ir_asm_virtual_isa1st::reorder_bb_shorten_jump(fundef);
        ir_asm_virtual_isa1st::scheduling(fundef);
    }
    let mut c = Default::default();
    for fundef in &virtasm.fundefs {
        fundef.collect_usage(&mut c);
    }
    Ok((virtasm, c))
}
