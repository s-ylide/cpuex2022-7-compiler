use std::collections::HashMap;

use ir_asm_ast_isa1st::StaticLibrary;
use once_cell::sync::Lazy;
use ty::{ConcTy, FnTy};
use typedefs::Label;

pub static ASM_LIBS: Lazy<StaticLibrary<Label>> = Lazy::new(|| {
    let src = include_str!("./asm/lib.s");
    ir_asm_parser_isa1st::parse_library(src).unwrap()
});

#[derive(Debug, Clone, Copy)]
pub enum LibFnTy {
    U2I,
    U2F,
    I2U,
    I2F,
    F2I,
    F2B,
    F2F,
    F2F2B,
    F2F2F,
}

impl LibFnTy {
    pub fn get_ty(&self) -> FnTy {
        use ConcTy::*;
        use LibFnTy::*;
        match self {
            U2I => FnTy {
                arg: vec![Unit],
                ret: Int,
            },
            U2F => FnTy {
                arg: vec![Unit],
                ret: Float,
            },
            I2U => FnTy {
                arg: vec![Int],
                ret: Unit,
            },
            I2F => FnTy {
                arg: vec![Int],
                ret: Float,
            },
            F2I => FnTy {
                arg: vec![Float],
                ret: Int,
            },
            F2B => FnTy {
                arg: vec![Float],
                ret: Bool,
            },
            F2F => FnTy {
                arg: vec![Float],
                ret: Float,
            },
            F2F2B => FnTy {
                arg: vec![Float, Float],
                ret: Bool,
            },
            F2F2F => FnTy {
                arg: vec![Float, Float],
                ret: Float,
            },
        }
    }
}

pub struct FnInfo {
    pub sig: LibFnTy,
    pub has_effect: bool,
}

impl FnInfo {
    pub fn new(sig: LibFnTy, has_effect: bool) -> Self {
        Self { sig, has_effect }
    }
}

pub static V_ASM_PERVASIVES: Lazy<HashMap<&'static str, FnInfo>> = Lazy::new(|| {
    use LibFnTy::*;
    HashMap::from_iter([
        ("sqrt", FnInfo::new(F2F, false)),
        ("fhalf", FnInfo::new(F2F, false)),
        ("fsgnj", FnInfo::new(F2F2F, false)),
        ("fsgnjx", FnInfo::new(F2F2F, false)),
        ("fsqr", FnInfo::new(F2F, false)),
        ("fabs", FnInfo::new(F2F, false)),
        ("fneg", FnInfo::new(F2F, false)),
        ("fless", FnInfo::new(F2F2B, false)),
        ("fiszero", FnInfo::new(F2B, false)),
        ("fispos", FnInfo::new(F2B, false)),
        ("fisneg", FnInfo::new(F2B, false)),
        ("floor", FnInfo::new(F2F, false)),
        ("int_of_float", FnInfo::new(F2I, false)),
        ("float_of_int", FnInfo::new(I2F, false)),
        ("print_int", FnInfo::new(I2U, true)),
        ("print_char", FnInfo::new(I2U, true)),
        ("read_int", FnInfo::new(U2I, true)),
        ("read_float", FnInfo::new(U2F, true)),
    ])
});
