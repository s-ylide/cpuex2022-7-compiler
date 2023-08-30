use ir_asm_ast_isa1st::abi::{FRegId, RegId, Register};

use crate::bit::{at, extract, mask, mask_lower};

struct RInstrBitAlign {
    opcode: u32,
    rd: u32,
    funct3: u32,
    rs1: u32,
    rs2: u32,
    funct7: u32,
}

struct IInstrBitAlign {
    opcode: u32,
    rd: u32,
    funct3: u32,
    rs1: u32,
    imm: u32,
}

#[allow(warnings)]
struct UInstrBitAlign {
    opcode: u32,
    rd: u32,
    imm: u32,
}

macro_rules! sanitize_value {
    ([@sanitize] $field:ident, $target:ident, $bitwidth:literal) => {
        #[cfg(debug_assertions)]
        if $target >= 1 << $bitwidth {
            panic!(
                "field `{}` must be within {}-bit, found {:#034b}",
                stringify!($field),
                $bitwidth,
                $target
            );
        }
    };
    ([@sanitize+] $field:ident, $target:ident, $bitwidth:literal) => {
        #[cfg(debug_assertions)]
        {
            let len = 32 - $bitwidth;
            let sign_ext = mask($target, $bitwidth..31);
            if sign_ext.count_ones() != 0 && sign_ext.count_ones() != len {
                panic!(
                    "field `{}` must be within {}-bit (with sign extention), found {:#034b}",
                    stringify!($field),
                    $bitwidth,
                    $target
                );
            }
        }
    };
}

#[inline]
pub fn r_instr(opcode: u32, rd: RegId, funct3: u32, rs1: RegId, rs2: RegId, funct7: u32) -> u32 {
    RInstrBitAlign {
        opcode,
        rd: rd.inner(),
        funct3,
        rs1: rs1.inner(),
        rs2: rs2.inner(),
        funct7,
    }
    .encode()
}

#[inline]
pub fn i_instr(opcode: u32, rd: RegId, funct3: u32, rs1: RegId, imm: u32) -> u32 {
    IInstrBitAlign {
        opcode,
        rd: rd.inner(),
        funct3,
        rs1: rs1.inner(),
        imm,
    }
    .encode()
}

#[cfg(not(feature = "isa_2nd"))]
#[inline]
pub fn i_instr_f7(opcode: u32, rd: RegId, funct3: u32, rs1: RegId, imm: u32, funct7: u32) -> u32 {
    sanitize_value!([@sanitize] imm, imm, 5);
    RInstrBitAlign {
        opcode,
        rd: rd.inner(),
        funct3,
        rs1: rs1.inner(),
        rs2: imm,
        funct7,
    }
    .encode()
}

cfg_if::cfg_if! {
    if #[cfg(feature = "isa_2nd")] {
        #[inline]
        fn s_common(opcode: u32, imm: u32, funct3: u32, rs1: RegId, rs2: u32) -> u32 {
            let imm_l = mask_lower(imm, 5);
            let imm_h = extract(imm, 6..12);
            RInstrBitAlign {
                opcode,
                rd: imm_l,
                funct3,
                rs1: rs1.inner(),
                rs2,
                funct7: imm_h,
            }
            .encode()
        }
    }
    else {
        #[inline]
        fn s_common(opcode: u32, imm: u32, funct3: u32, rs1: RegId, rs2: u32) -> u32 {
            let imm_l = mask_lower(imm, 4);
            let imm_h = extract(imm, 5..11);
            RInstrBitAlign {
                opcode,
                rd: imm_l,
                funct3,
                rs1: rs1.inner(),
                rs2,
                funct7: imm_h,
            }
            .encode()
        }
    }
}

#[inline]
pub fn s_instr(opcode: u32, imm: u32, funct3: u32, rs1: RegId, rs2: RegId) -> u32 {
    s_common(opcode, imm, funct3, rs1, rs2.inner())
}

cfg_if::cfg_if! {
    if #[cfg(feature = "isa_2nd")] {
        #[inline]
        fn b_common(opcode: u32, imm: u32, funct3: u32, rs1: u32, rs2: u32) -> u32 {
            sanitize_value!([@sanitize+] imm, imm, 14);
            let rd = mask(imm, 2..5) | extract(imm, 12..13);
            let f6 = extract(imm, 6..11);
            RInstrBitAlign {
                opcode,
                rd,
                funct3,
                rs1,
                rs2,
                funct7: f6 | (at(imm, 14) << 6),
            }
            .encode()
        }
    }
    else {
        #[inline]
        fn b_common(opcode: u32, imm: u32, funct3: u32, rs1: u32, rs2: u32) -> u32 {
            sanitize_value!([@sanitize+] imm, imm, 12);
            let rd = mask(imm, 1..4) | at(imm, 11);
            let f6 = extract(imm, 5..10);
            RInstrBitAlign {
                opcode,
                rd,
                funct3,
                rs1,
                rs2,
                funct7: f6 | (at(imm, 12) << 6),
            }
            .encode()
        }
    }
}

#[inline]
pub fn b_instr(opcode: u32, imm: u32, funct3: u32, rs1: RegId, rs2: RegId) -> u32 {
    b_common(opcode, imm, funct3, rs1.inner(), rs2.inner())
}

#[cfg(feature = "isa_2nd")]
#[inline]
pub fn p_instr(imm: u32, funct3: u32, rs1: RegId, imm2: u32) -> u32 {
    sanitize_value!([@sanitize+] imm2, imm2, 6);
    b_common(0b1100, imm, funct3, rs1.inner(), mask_lower(imm2, 5))
}

cfg_if::cfg_if! {
    if #[cfg(feature = "isa_2nd")] {
        #[inline]
        pub fn j_instr(opcode: u32, rd: RegId, imm: u32) -> u32 {
            sanitize_value!([@sanitize+] imm, imm, 23);
            let rs2 = mask(imm, 2..5) | extract(imm, 12..13);
            let funct3 = extract(imm, 14..16);
            let rs1 = extract(imm, 17..22);
            let f6 = extract(imm, 6..11);
            RInstrBitAlign {
                opcode,
                rd: rd.inner(),
                funct3,
                rs1,
                rs2,
                funct7: f6 | (at(imm, 23) << 6),
            }
            .encode()
        }
    }
    else {
        #[inline]
        pub fn j_instr(opcode: u32, rd: RegId, imm: u32) -> u32 {
            sanitize_value!([@sanitize+] imm, imm, 20);
            let rs2 = mask(imm, 1..4) | at(imm, 11);
            let funct3 = extract(imm, 12..14);
            let rs1 = extract(imm, 15..19);
            let f6 = extract(imm, 5..10);
            RInstrBitAlign {
                opcode,
                rd: rd.inner(),
                funct3,
                rs1,
                rs2,
                funct7: f6 | (at(imm, 20) << 6),
            }
            .encode()
        }
    }
}

#[inline]
pub fn io_instr(opcode: u32, rd: u32, funct3: u32, rs: u32) -> u32 {
    RInstrBitAlign {
        opcode,
        rd,
        funct3,
        rs1: rs,
        rs2: 0,
        funct7: 0,
    }
    .encode()
}

#[inline]
pub fn e_instr(opcode: u32, rd: FRegId, rm: u32, rs1: FRegId, rs2: FRegId, funct5: u32) -> u32 {
    RInstrBitAlign {
        opcode,
        rd: rd.inner(),
        funct3: rm,
        rs1: rs1.inner(),
        rs2: rs2.inner(),
        funct7: funct5 << 2,
    }
    .encode()
}

#[cfg(feature = "isa_2nd")]
#[inline]
pub fn g_instr(rd: FRegId, funct3: u32, rs1: FRegId, rs2: FRegId, rs3: FRegId) -> u32 {
    RInstrBitAlign {
        opcode: 0b0001,
        rd: rd.inner(),
        funct3,
        rs1: rs1.inner(),
        rs2: rs2.inner(),
        funct7: rs3.inner(),
    }
    .encode()
}

#[inline]
pub fn h_instr(opcode: u32, rd: FRegId, rm: u32, rs1: FRegId, funct5: u32) -> u32 {
    e_instr(opcode, rd, rm, rs1, FRegId::new(0), funct5)
}

#[inline]
pub fn k_instr(opcode: u32, rd: RegId, rm: u32, rs1: FRegId, rs2: FRegId, funct5: u32) -> u32 {
    RInstrBitAlign {
        opcode,
        rd: rd.inner(),
        funct3: rm,
        rs1: rs1.inner(),
        rs2: rs2.inner(),
        funct7: funct5 << 2 | 0b01,
    }
    .encode()
}

#[inline]
pub fn x_instr(opcode: u32, rd: FRegId, funct3: u32, rs1: RegId, funct5: u32) -> u32 {
    RInstrBitAlign {
        opcode,
        rd: rd.inner(),
        funct3,
        rs1: rs1.inner(),
        rs2: 0,
        funct7: funct5 << 2 | 0b10,
    }
    .encode()
}

#[inline]
pub fn y_instr(opcode: u32, rd: RegId, funct3: u32, rs1: FRegId, funct5: u32) -> u32 {
    RInstrBitAlign {
        opcode,
        rd: rd.inner(),
        funct3,
        rs1: rs1.inner(),
        rs2: 0,
        funct7: funct5 << 2 | 0b01,
    }
    .encode()
}

#[inline]
pub fn w_instr(opcode: u32, imm: u32, funct3: u32, rs1: FRegId, rs2: FRegId) -> u32 {
    b_common(opcode, imm, funct3, rs1.inner(), rs2.inner())
}

#[inline]
pub fn v_instr(opcode: u32, imm: u32, funct3: u32, rs1: FRegId) -> u32 {
    b_common(opcode, imm, funct3, rs1.inner(), 0)
}

#[inline]
pub fn fi_instr(opcode: u32, funct3: u32, rd: FRegId, imm: u32, rs1: RegId) -> u32 {
    IInstrBitAlign {
        opcode,
        rd: rd.inner(),
        funct3,
        rs1: rs1.inner(),
        imm,
    }
    .encode()
}

#[inline]
pub fn fs_instr(opcode: u32, funct3: u32, rs2: FRegId, imm: u32, rs1: RegId) -> u32 {
    s_common(opcode, imm, funct3, rs1, rs2.inner())
}

macro_rules! sani_encode {
    (defer $buf:ident; $i:ident. $($t:tt)*) => {
        let mut $buf;
        _sani_encode!([$i,$buf @first] $($t)*);
        $buf
    };
}

macro_rules! _sani_encode {
    ([$i:ident,$buf:ident,$acc:expr]) => {};
    ([$i:ident,$buf:ident @first] $field:ident : $l:literal; $($t:tt)*) => {
        let b = $i.$field;
        $buf = b;
        sanitize_value!([@sanitize] $field, b, $l);
        _sani_encode!([$i,$buf,$l] $($t)*)
    };
    ([$i:ident,$buf:ident,$acc:expr] $field:ident : $l:literal; $($t:tt)*) => {
        let b = $i.$field;
        $buf += b << $acc;
        sanitize_value!([@sanitize] $field, b, $l);
        _sani_encode!([$i,$buf,$acc + $l] $($t)*)
    };
    ([$i:ident,$buf:ident,$acc:expr] $field:ident : $l:literal+; $($t:tt)*) => {
        let b = $i.$field;
        $buf += b << $acc;
        sanitize_value!([@sanitize+] $field, b, $l);
        _sani_encode!([$i,$buf,$acc + $l] $($t)*)
    };
}

cfg_if::cfg_if! {
    if #[cfg(feature = "isa_2nd")] {
        impl RInstrBitAlign {
            #[inline]
            fn encode(self) -> u32 {
                sani_encode! {
                    defer r;
                    self.
                        opcode: 4;
                        rd: 6;
                        funct3: 3;
                        rs1: 6;
                        rs2: 6;
                        funct7: 7;
                }
            }
        }
    } else {
        impl RInstrBitAlign {
            #[inline]
            fn encode(self) -> u32 {
                sani_encode! {
                    defer r;
                    self.
                        opcode: 7;
                        rd: 5;
                        funct3: 3;
                        rs1: 5;
                        rs2: 5;
                        funct7: 7;
                }
            }
        }
    }
}

cfg_if::cfg_if! {
    if #[cfg(feature = "isa_2nd")] {
        impl IInstrBitAlign {
            #[inline]
            fn encode(self) -> u32 {
                sani_encode! {
                    defer r;
                    self.
                        opcode: 4;
                        rd: 6;
                        funct3: 3;
                        rs1: 6;
                        imm: 13+;
                }
            }
        }
    } else {
        impl IInstrBitAlign {
            #[inline]
            fn encode(self) -> u32 {
                sani_encode! {
                    defer r;
                    self.
                        opcode: 7;
                        rd: 5;
                        funct3: 3;
                        rs1: 5;
                        imm: 12+;
                }
            }
        }
    }
}

cfg_if::cfg_if! {
    if #[cfg(feature = "isa_2nd")] {
    } else {
        #[cfg(test)]
        mod tests {
            use super::*;

            #[test]
            fn test_rinstr_encode() {
                // or x4, x5, x6
                let r = RInstrBitAlign {
                    opcode: 0b0110011,
                    rd: 0b00100,
                    funct3: 0b110,
                    rs1: 0b00101,
                    rs2: 0b00110,
                    funct7: 0b0000000,
                };
                assert_eq!(r.encode(), 0x0062E233);
            }
        }
    }
}
