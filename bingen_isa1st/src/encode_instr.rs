use crate::{bit::*, format::*, instr::*, AsConst};
use ir_asm_ast_isa1st::{abi::Register, *};

const IMM_SHOULD_BE_CONST: &str = "imm should be constant at this stage";

impl<Offset: AsConst<Const = Addr>> BaseInstr<Offset> {
    // encode calculating %hi or %lo
    pub fn encode(self) -> u32 {
        use BaseInstr::*;
        use IOInstr::*;
        match self {
            R {
                instr,
                rd,
                rs1,
                rs2,
            } => {
                use RInstr::*;
                cfg_if::cfg_if! {
                    if #[cfg(feature = "isa_2nd")] {
                        let funct3 = match instr {
                            Add => 0x0,
                            Xor => 0x4,
                            Min => 0x1,
                            Max => 0x3,
                        };
                        r_instr(0b0000, rd, funct3, rs1, rs2, 0)
                    } else {
                        let (funct3, funct7) = match instr {
                            Add => (0x0, 0x00),
                            Sub => (0x0, 0x20),
                            Xor => (0x4, 0x00),
                            Or => (0x6, 0x00),
                            And => (0x7, 0x00),
                            Sll => (0x1, 0x00),
                            Sra => (0x5, 0x20),
                            Slt => (0x2, 0x00),
                        };
                        r_instr(0b0110011, rd, funct3, rs1, rs2, funct7)
                    }
                }
            }
            I {
                instr,
                rd,
                rs1,
                imm,
            } => {
                use IInstr::*;
                cfg_if::cfg_if! {
                    if #[cfg(feature = "isa_2nd")] {
                        let imm = mask_lower(imm, 12);
                        let (opcode, funct3) = match instr {
                            Addi => (0b0010, 0x0),
                            Xori => (0b0010, 0x4),
                            Slli => (0b0010, 0x2),
                            Lw(region) => (0b0110, region.f3()),
                            Jalr => (0b1010, 0x0),
                        };
                        i_instr(opcode, rd, funct3, rs1, imm)
                    } else {
                        let imm = mask_lower(imm, 11);
                        let (opcode, funct3, funct7) = match instr {
                            Addi => (0b0010011, 0x0, None),
                            Xori => (0b0010011, 0x4, None),
                            Ori => (0b0010011, 0x6, None),
                            Andi => (0b0010011, 0x7, None),
                            Slli => (0b0010011, 0x1, Some(0x00)),
                            Srai => (0b0010011, 0x5, Some(0x20)),
                            Slti => (0b0010011, 0x2, None),
                            Lw(_) => (0b0000011, 0x2, None),
                            Jalr => (0b1100111, 0x0, None),
                        };
                        match funct7 {
                            None => i_instr(opcode, rd, funct3, rs1, imm),
                            Some(funct7) => i_instr_f7(opcode, rd, funct3, rs1, imm, funct7),
                        }
                    }
                }
            }
            S {
                instr,
                rs1,
                rs2,
                imm,
            } => {
                use SInstr::*;
                cfg_if::cfg_if! {
                    if #[cfg(feature = "isa_2nd")] {
                        let funct3 = match instr {
                            Sw(region) => region.f3(),
                        };
                        s_instr(0b0100, imm, funct3, rs1, rs2)
                    }
                    else {
                        let funct3 = match instr {
                            Sw(_) => 0x2,
                        };
                        s_instr(0b0100011, imm, funct3, rs1, rs2)
                    }
                }
            }
            B {
                instr,
                rs1,
                rs2,
                imm,
            } => {
                use BInstr::*;
                cfg_if::cfg_if! {
                    if #[cfg(feature = "isa_2nd")] {
                        let funct3 = match instr {
                            Beq => 0x0,
                            Bne => 0x1,
                            Blt => 0x4,
                            Bge => 0x5,
                            Bxor => 0x2,
                            Bxnor => 0x3,
                        };
                        let imm = imm.as_const().expect(IMM_SHOULD_BE_CONST);
                        b_instr(0b1000, imm, funct3, rs1, rs2)
                    }
                    else {
                        let funct3 = match instr {
                            Beq => 0x0,
                            Bne => 0x1,
                            Blt => 0x4,
                            Bge => 0x5,
                        };
                        let imm = imm.as_const().expect(IMM_SHOULD_BE_CONST);
                        b_instr(0b1100011, imm, funct3, rs1, rs2)
                    }
                }
            }
            #[cfg(feature = "isa_2nd")]
            P {
                instr,
                rs1,
                imm,
                imm2,
            } => {
                use PInstr::*;
                let funct3 = match instr {
                    Beqi => 0x0,
                    Bnei => 0x1,
                    Blti => 0x4,
                    Bgei => 0x5,
                    Bgti => 0x6,
                    Blei => 0x7,
                };
                let imm = imm.as_const().expect(IMM_SHOULD_BE_CONST);
                p_instr(imm, funct3, rs1, imm2)
            }
            J { instr, rd, imm } => {
                use JInstr::*;
                let opcode = match instr {
                    #[cfg(feature = "isa_2nd")]
                    Jal => 0b1110,
                    #[cfg(not(feature = "isa_2nd"))]
                    Jal => 0b1101111,
                };
                let imm = imm.as_const().expect(IMM_SHOULD_BE_CONST);
                j_instr(opcode, rd, imm)
            }
            #[cfg(feature = "isa_2nd")]
            IO(io) => match io {
                Inw { rd } => io_instr(0b0011, rd.inner(), 0b001, 0),
                Outb { rs } => io_instr(0b0011, 0, 0b010, rs.inner()),
                Finw { rd } => io_instr(0b0011, rd.inner(), 0b100, 0),
            },
            #[cfg(not(feature = "isa_2nd"))]
            IO(io) => match io {
                Outb { rs } => io_instr(0b0101011, 0, 0b001, rs.inner()),
                Inw { rd } => io_instr(0b0001011, rd.inner(), 0b000, 0),
                Finw { rd } => io_instr(0b0001111, rd.inner(), 0b000, 0),
            },
            F(f) => Self::encode_f(f),
            #[cfg(feature = "isa_2nd")]
            Misc {
                instr: MiscInstr::End,
            } => 1 << 31,
            #[cfg(not(feature = "isa_2nd"))]
            Misc {
                instr: MiscInstr::End,
            } => 0,
        }
    }

    // encode calculating %hi or %lo
    fn encode_f(f: FInstr<Offset>) -> u32 {
        use FInstr::*;
        match f {
            E {
                instr,
                rd,
                rs1,
                rs2,
            } => {
                use EInstr::*;
                let funct5 = match instr {
                    Fadd => 0b00000,
                    Fsub => 0b00001,
                    Fmul => 0b00010,
                    Fdiv => 0b00011,
                    Fsgnj => 0b00110,
                    Fsgnjn => 0b00111,
                    Fsgnjx => 0b01000,
                };
                cfg_if::cfg_if! {
                    if #[cfg(feature = "isa_2nd")] {
                        e_instr(0b0001, rd, 0b000, rs1, rs2, funct5)
                    }
                    else {
                        e_instr(0b1010011, rd, 0b000, rs1, rs2, funct5)
                    }
                }
            }
            #[cfg(feature = "isa_2nd")]
            G {
                instr,
                rd,
                rs1,
                rs2,
                rs3,
            } => {
                use GInstr::*;
                let funct3 = match instr {
                    Fmadd => 0b001,
                    Fmsub => 0b010,
                    Fnmadd => 0b101,
                    Fnmsub => 0b110,
                };
                g_instr(rd, funct3, rs1, rs2, rs3)
            }
            H { instr, rd, rs1 } => {
                use HInstr::*;
                cfg_if::cfg_if! {
                    if #[cfg(feature = "isa_2nd")] {
                        let funct5 = match instr {
                            Fsqrt  => 0b00100,
                            Fhalf  => 0b00101,
                            Ffrac  => 0b01100,
                            Finv   => 0b01011,
                            Ffloor => 0b01001,
                        };
                        h_instr(0b0001, rd, 0b000, rs1, funct5)
                    }
                    else {
                        let funct5 = match instr {
                            Fsqrt  => 0b00100,
                            Fhalf  => 0b00101,
                            Ffloor => 0b10000,
                        };
                        h_instr(0b1010011, rd, 0b000, rs1, funct5)
                    }
                }
            }
            K {
                instr,
                rd,
                rs1,
                rs2,
            } => {
                use KInstr::*;
                let funct5 = match instr {
                    Flt => 0b10100,
                };
                cfg_if::cfg_if! {
                    if #[cfg(feature = "isa_2nd")] {
                        k_instr(0b0001, rd, 0b001, rs1, rs2, funct5)
                    }
                    else {
                        k_instr(0b1010011, rd, 0b001, rs1, rs2, funct5)
                    }
                }
            }
            X { instr, rd, rs1 } => {
                use XInstr::*;
                cfg_if::cfg_if! {
                    if #[cfg(feature = "isa_2nd")] {
                        let funct5 = match instr {
                            Fitof => 0b11001,
                        };
                        x_instr(0b0001, rd, 0x000, rs1, funct5)
                    }
                    else {
                        let funct5 = match instr {
                            Fitof => 0b01001,
                        };
                        x_instr(0b1010011, rd, 0x000, rs1, funct5)
                    }
                }
            }
            Y { instr, rd, rs1 } => {
                use YInstr::*;
                let (funct3, funct5) = match instr {
                    Fiszero => (0b100, 0b10100),
                    Fispos => (0b101, 0b10100),
                    Fisneg => (0b110, 0b10100),
                    Fftoi => (0b000, 0b10001),
                };
                cfg_if::cfg_if! {
                    if #[cfg(feature = "isa_2nd")] {
                        y_instr(0b0001, rd, funct3, rs1, funct5)
                    }
                    else {
                        y_instr(0b1010011, rd, funct3, rs1, funct5)
                    }
                }
            }
            W {
                instr,
                rs1,
                rs2,
                imm,
            } => {
                use WInstr::*;
                let funct3 = match instr {
                    Fblt => 0b001,
                    Fbge => 0b010,
                };
                let imm = imm.as_const().expect(IMM_SHOULD_BE_CONST);
                cfg_if::cfg_if! {
                    if #[cfg(feature = "isa_2nd")] {
                        w_instr(0b1001, imm, funct3, rs1, rs2)
                    }
                    else {
                        w_instr(0b1010111, imm, funct3, rs1, rs2)
                    }
                }
            }
            V { instr, rs1, imm } => {
                use VInstr::*;
                let funct3 = match instr {
                    Fbeqz => 0b100,
                    Fbnez => 0b111,
                };
                let imm = imm.as_const().expect(IMM_SHOULD_BE_CONST);
                cfg_if::cfg_if! {
                    if #[cfg(feature = "isa_2nd")] {
                        v_instr(0b1001, imm, funct3, rs1)
                    }
                    else {
                        v_instr(0b1010111, imm, funct3, rs1)
                    }
                }
            }
            #[cfg(feature = "isa_2nd")]
            Flw {
                region,
                rd,
                rs1,
                imm,
            } => fi_instr(0b0111, region.f3(), rd, imm, rs1),
            #[cfg(feature = "isa_2nd")]
            Fsw {
                region,
                rs2,
                rs1,
                imm,
            } => fs_instr(0b0101, region.f3(), rs2, imm, rs1),
            #[cfg(not(feature = "isa_2nd"))]
            Flw {
                region: _,
                rd,
                rs1,
                imm,
            } => fi_instr(0b0000111, 0b010, rd, imm, rs1),
            #[cfg(not(feature = "isa_2nd"))]
            Fsw {
                region: _,
                rs2,
                rs1,
                imm,
            } => fs_instr(0b0100111, 0b010, rs2, imm, rs1),
        }
    }
}
