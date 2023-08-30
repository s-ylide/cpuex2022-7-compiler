use ir_asm_ast_isa1st::{
    abi::{FRegId, RegId},
    MemRegion,
};

pub enum BaseInstr<Offset> {
    R {
        instr: RInstr,
        rd: RegId,
        rs1: RegId,
        rs2: RegId,
    },
    I {
        instr: IInstr,
        rd: RegId,
        rs1: RegId,
        imm: u32,
    },
    S {
        instr: SInstr,
        rs1: RegId,
        rs2: RegId,
        imm: u32,
    },
    B {
        instr: BInstr,
        rs1: RegId,
        rs2: RegId,
        imm: Offset,
    },
    #[cfg(feature = "isa_2nd")]
    P {
        instr: PInstr,
        rs1: RegId,
        imm: Offset,
        imm2: u32,
    },
    J {
        instr: JInstr,
        rd: RegId,
        imm: Offset,
    },
    F(FInstr<Offset>),
    IO(IOInstr),
    Misc {
        instr: MiscInstr,
    },
}

pub enum FInstr<Offset> {
    E {
        instr: EInstr,
        rd: FRegId,
        rs1: FRegId,
        rs2: FRegId,
    },
    #[allow(unused)]
    #[cfg(feature = "isa_2nd")]
    G {
        instr: GInstr,
        rd: FRegId,
        rs1: FRegId,
        rs2: FRegId,
        rs3: FRegId,
    },
    H {
        instr: HInstr,
        rd: FRegId,
        rs1: FRegId,
    },
    K {
        instr: KInstr,
        rd: RegId,
        rs1: FRegId,
        rs2: FRegId,
    },
    X {
        instr: XInstr,
        rd: FRegId,
        rs1: RegId,
    },
    Y {
        instr: YInstr,
        rd: RegId,
        rs1: FRegId,
    },
    W {
        instr: WInstr,
        rs1: FRegId,
        rs2: FRegId,
        imm: Offset,
    },
    V {
        instr: VInstr,
        rs1: FRegId,
        imm: Offset,
    },
    /// I
    Flw {
        region: MemRegion,
        rd: FRegId,
        rs1: RegId,
        imm: u32,
    },
    /// S
    Fsw {
        region: MemRegion,
        rs2: FRegId,
        rs1: RegId,
        imm: u32,
    },
}

pub enum IOInstr {
    Outb { rs: RegId },
    Inw { rd: RegId },
    Finw { rd: FRegId },
}

pub enum MiscInstr {
    End,
}

cfg_if::cfg_if! {
    if #[cfg(feature = "isa_2nd")] {
        pub enum RInstr {
            Add,
            Xor,
            Min,
            Max,
        }
    } else {
        pub enum RInstr {
            Add,
            Sub,
            Xor,
            Or,
            And,
            Sll,
            Sra,
            Slt,
        }
    }
}

cfg_if::cfg_if! {
    if #[cfg(feature = "isa_2nd")] {
        pub enum IInstr {
            Addi,
            Xori,
            Slli,
            Lw(MemRegion),
            Jalr,
        }
    } else {
        pub enum IInstr {
            Addi,
            Xori,
            Ori,
            Andi,
            Slli,
            Srai,
            Slti,
            Lw(MemRegion),
            Jalr,
        }
    }
}

pub enum SInstr {
    Sw(MemRegion),
}

pub enum BInstr {
    Beq,
    Bne,
    Blt,
    Bge,
    #[cfg(feature = "isa_2nd")]
    Bxor,
    #[cfg(feature = "isa_2nd")]
    Bxnor,
}

#[cfg(feature = "isa_2nd")]
pub enum PInstr {
    Beqi,
    Bnei,
    Blti,
    Bgei,
    Bgti,
    Blei,
}

pub enum JInstr {
    Jal,
}

pub enum EInstr {
    Fadd,
    Fsub,
    Fmul,
    Fdiv,
    Fsgnj,
    Fsgnjn,
    Fsgnjx,
}

#[allow(unused)]
#[cfg(feature = "isa_2nd")]
pub enum GInstr {
    Fmadd,
    Fmsub,
    Fnmadd,
    Fnmsub,
}

cfg_if::cfg_if! {
    if #[cfg(feature = "isa_2nd")] {
        pub enum HInstr {
            Fsqrt,
            Fhalf,
            #[allow(unused)]
            Ffrac,
            Finv,
            Ffloor,
        }
    }
    else {
        pub enum HInstr {
            Fsqrt,
            Fhalf,
            Ffloor,
        }
    }
}

pub enum KInstr {
    Flt,
}

pub enum XInstr {
    Fitof,
}

pub enum YInstr {
    Fiszero,
    Fispos,
    Fisneg,
    Fftoi,
}

pub enum WInstr {
    Fblt,
    Fbge,
}

pub enum VInstr {
    Fbeqz,
    Fbnez,
}
