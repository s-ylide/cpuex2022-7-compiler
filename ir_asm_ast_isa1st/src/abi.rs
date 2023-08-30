use std::{fmt::Display, hash::Hash};

use ast::ConstKind;
use once_cell::sync::Lazy;
use ordered_float::NotNan;
use ty::ConcTy;

pub trait Register: Eq + Hash + Clone + Copy + Display + 'static {
    fn zero() -> &'static Self;
    /// register used as n-th argument.
    fn arg_nth(n: usize) -> Self;
    fn inner(&self) -> u32;
}

#[derive(Debug, PartialEq, Clone, Copy, Eq, Hash, PartialOrd, Ord)]
pub struct RegId(u32);

impl RegId {
    #[inline]
    pub const fn new(i: u32) -> Self {
        Self(i)
    }
}

impl Register for RegId {
    fn zero() -> &'static Self {
        &REG_X0
    }

    fn arg_nth(n: usize) -> Self {
        #[cfg(debug_assertions)]
        if n > 8 {
            panic!("too long argument")
        }
        RegId::new((n + 10) as u32)
    }
    fn inner(&self) -> u32 {
        self.0
    }
}

#[cfg(not(feature = "isa_2nd"))]
pub static ABINAME_TABLE: [&str; 32] = [
    "zero", "ra", "sp", "gp", "hp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6",
];

#[cfg(feature = "isa_2nd")]
pub static ABINAME_TABLE: [&str; 64] = [
    "zero", "ra", "sp", "gp", "hp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4",
    "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4",
    "t5", "t6", "x32", "x33", "x34", "x35", "x36", "x37", "x38", "x39", "x40", "x41", "x42", "x43",
    "x44", "x45", "x46", "x47", "x48", "x49", "x50", "x51", "x52", "x53", "x54", "x55", "x56",
    "x57", "x58", "x59", "x60", "x61", "x62", "x63",
];

impl Display for RegId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = ABINAME_TABLE[self.0 as usize];
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone, Copy, Eq, Hash, PartialOrd, Ord)]
pub struct FRegId(u32);

impl FRegId {
    #[inline]
    pub const fn new(i: u32) -> Self {
        Self(i)
    }
}

impl Register for FRegId {
    fn zero() -> &'static Self {
        &REG_F0
    }

    fn arg_nth(n: usize) -> Self {
        #[cfg(debug_assertions)]
        if n > 8 {
            panic!("too long argument")
        }
        FRegId::new((n + 10) as u32)
    }
    fn inner(&self) -> u32 {
        self.0
    }
}

#[cfg(not(feature = "isa_2nd"))]
pub static F_ABINAME_TABLE: [&str; 32] = [
    "fzero", "fone", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7", "fs0", "fs1", "fa0", "fa1", "fa2",
    "fa3", "fa4", "fa5", "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7", "fs8", "fs9",
    "fs10", "fs11", "ft8", "ft9", "ft10", "ft11",
];

#[cfg(feature = "isa_2nd")]
pub static F_ABINAME_TABLE: [&str; 64] = [
    "fzero", "fone", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7", "fs0", "fs1", "fa0", "fa1", "fa2",
    "fa3", "fa4", "fa5", "fa6", "fa7", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7", "fs8", "fs9",
    "fs10", "fs11", "ft8", "ft9", "ft10", "ft11", "f32", "f33", "f34", "f35", "f36", "f37", "f38",
    "f39", "f40", "f41", "f42", "f43", "f44", "f45", "f46", "f47", "f48", "f49", "f50", "f51",
    "f52", "f53", "f54", "f55", "f56", "f57", "f58", "f59", "f60", "f61", "f62", "f63",
];

impl Display for FRegId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = F_ABINAME_TABLE[self.0 as usize];
        f.write_str(s)
    }
}

#[derive(Debug, Clone)]
pub enum RegKind {
    Int,
    Float,
}

impl Display for RegKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RegKind::Int => write!(f, "i32"),
            RegKind::Float => write!(f, "f32"),
        }
    }
}

impl TryFrom<ty::ConcTy> for RegKind {
    type Error = ();

    fn try_from(value: ty::ConcTy) -> Result<Self, Self::Error> {
        Self::from_concty(&value).ok_or(())
    }
}

impl RegKind {
    pub fn from_concty(value: &ty::ConcTy) -> Option<Self> {
        match value {
            ConcTy::Float => Some(RegKind::Float),
            ConcTy::Bool
            | ConcTy::Int
            | ConcTy::Tuple(_)
            | ConcTy::Array(..)
            | ConcTy::Fun(_, _) => Some(RegKind::Int),
            _ => None,
        }
    }
}

pub fn addr_sizeof_ty(_: &ty::ConcTy) -> usize {
    4
}

pub fn sizeof_concty(c: &ty::ConcTy) -> Option<usize> {
    match c {
        ConcTy::Unit => Some(0),
        ConcTy::Bool => Some(4),
        ConcTy::Int => Some(4),
        ConcTy::Float => Some(4),
        ConcTy::Fun(..) => None,
        ConcTy::Tuple(ts) => Some(ts.iter().map(addr_sizeof_ty).sum()),
        ConcTy::Array(t, c) => Some(addr_sizeof_ty(t) * (*c)?),
    }
}

#[derive(Debug, Clone)]
pub enum ConstSource {
    Int(IConstSource),
    Float(FConstSource),
}

impl ConstSource {
    pub fn from_const(c: ConstKind) -> Self {
        match c {
            ConstKind::Unit => unreachable!(),
            ConstKind::Bool(_) => unreachable!(),
            ConstKind::Int(i) => Self::Int(match i {
                0 => IConstSource::Register(REG_X0),
                i => IConstSource::Value(i),
            }),
            ConstKind::Float(f) => Self::Float(FConstSource::from_f32(f)),
        }
    }
}

#[derive(Debug, Clone)]
pub enum IConstSource {
    Value(i32),
    Register(RegId),
}

#[derive(Debug, Clone)]
pub enum FConstSource {
    Value(NotNan<f32>),
    MovF(FRegId),
    Fneg(FRegId),
}

impl FConstSource {
    pub fn from_f32(f: NotNan<f32>) -> Self {
        if f == 0.0 {
            FConstSource::MovF(REG_F0)
        } else if f == 1.0 {
            FConstSource::MovF(REG_F1)
        } else if f == -1.0 {
            FConstSource::Fneg(REG_F1)
        } else {
            FConstSource::Value(f)
        }
    }
}

#[cfg(not(feature = "isa_2nd"))]
static FREE_I_REGS: Lazy<Vec<RegId>> = Lazy::new(|| {
    let nums = [3..=3, 5..=9, 28..=30, 18..=27, 10..=17];
    nums.into_iter().flatten().map(RegId::new).collect()
});

#[cfg(feature = "isa_2nd")]
static FREE_I_REGS: Lazy<Vec<RegId>> = Lazy::new(|| {
    let nums = [3..=3, 5..=9, 28..=30, 18..=27, 32..=63, 10..=17];
    nums.into_iter().flatten().map(RegId::new).collect()
});

/// enumerates free caller-save registers. temporary registers come first
pub fn iregs() -> &'static Vec<RegId> {
    &FREE_I_REGS
}

#[cfg(not(feature = "isa_2nd"))]
static FREE_F_REGS: Lazy<Vec<FRegId>> = Lazy::new(|| {
    let nums = [2..=9, 28..=30, 18..=27, 10..=17];
    nums.into_iter().flatten().map(FRegId::new).collect()
});

#[cfg(feature = "isa_2nd")]
static FREE_F_REGS: Lazy<Vec<FRegId>> = Lazy::new(|| {
    let nums = [2..=9, 28..=30, 18..=27, 32..=63, 10..=17];
    nums.into_iter().flatten().map(FRegId::new).collect()
});

/// enumerates caller-save registers. temporary registers come first
pub fn fregs() -> &'static Vec<FRegId> {
    &FREE_F_REGS
}

pub const REG_X0: RegId = RegId::new(0);
pub const REG_RA: RegId = RegId::new(1);
pub const REG_SP: RegId = RegId::new(2);
pub const REG_HP: RegId = RegId::new(4);
pub const REG_A0: RegId = RegId::new(10);
pub const REG_STASH: RegId = RegId::new(31);
pub const REG_F0: FRegId = FRegId::new(0);
pub const REG_F1: FRegId = FRegId::new(1);
pub const REG_FA0: FRegId = FRegId::new(10);
pub const REG_FSTASH: FRegId = FRegId::new(31);
