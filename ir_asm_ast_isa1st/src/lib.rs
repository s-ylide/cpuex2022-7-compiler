use std::{
    borrow::Borrow,
    collections::{HashMap, VecDeque},
    fmt::Display,
    hash::Hash,
};

use abi::{FRegId, RegId};
use ast::ConstKind;
use ordered_float::NotNan;
use ty::ConcTy;

pub mod abi;

#[derive(Debug, Clone)]
pub enum CompileTimeConst<Label> {
    AddressOf(Label),
    Int(i32),
    Float(NotNan<f32>),
}

impl<Label: Display> Display for CompileTimeConst<Label> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileTimeConst::AddressOf(l) => write!(f, "&{l}"),
            CompileTimeConst::Int(i) => write!(f, "{i}"),
            CompileTimeConst::Float(ff) => write!(f, "{ff}"),
        }
    }
}

impl<Label> CompileTimeConst<Label> {
    pub fn try_from_constkind(c: ConstKind) -> Option<Self> {
        use CompileTimeConst::*;
        match c {
            ConstKind::Unit => None,
            ConstKind::Bool(_) => None,
            ConstKind::Int(i) => Some(Int(i)),
            ConstKind::Float(f) => Some(Float(f)),
        }
    }

    pub fn as_address_of(&self) -> Option<&Label> {
        if let Self::AddressOf(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct GlobalVarArray<Label> {
    pub count: i32,
    pub data: CompileTimeConst<Label>,
    pub modification: HashMap<i32, CompileTimeConst<Label>>,
}

impl<Label> GlobalVarArray<Label> {
    pub fn get(&self, c: &i32) -> &CompileTimeConst<Label> {
        self.modification.get(c).unwrap_or(&self.data)
    }
}

impl<Label> GlobalVarArray<Label> {
    pub fn new(count: i32, data: CompileTimeConst<Label>) -> Self {
        Self {
            count,
            data,
            modification: HashMap::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum GlobalVarValue<Label> {
    Array(GlobalVarArray<Label>),
    EmptyArray,
    Tuple(Vec<CompileTimeConst<Label>>),
    Const(CompileTimeConst<Label>),
}

impl<Label> GlobalVarValue<Label> {
    pub fn as_array_mut(&mut self) -> Option<&mut GlobalVarArray<Label>> {
        if let Self::Array(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_array(&self) -> Option<&GlobalVarArray<Label>> {
        if let Self::Array(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_cconst(&self) -> Vec<&CompileTimeConst<Label>> {
        match self {
            GlobalVarValue::Array(GlobalVarArray {
                data, modification, ..
            }) => {
                let mut r = vec![data];
                r.extend(modification.values());
                r
            }
            GlobalVarValue::EmptyArray => Vec::new(),
            GlobalVarValue::Tuple(t) => t.iter().collect(),
            GlobalVarValue::Const(c) => vec![c],
        }
    }
}

#[derive(Debug, Clone)]
pub struct GlobalVar<Label> {
    pub name: Label,
    pub size: usize,
    pub ty: ConcTy,
    pub value: GlobalVarValue<Label>,
}

pub type FloatConstMap<Label> = HashMap<u32, (Label, NotNan<f32>)>;

#[derive(Debug, Clone)]
pub struct GlobalVarMap<Label> {
    index: HashMap<Label, usize>,
    pub data: VecDeque<GlobalVar<Label>>,
}

impl<Label> GlobalVarMap<Label> {
    pub fn new() -> Self {
        Self {
            index: Default::default(),
            data: Default::default(),
        }
    }
    pub fn values(&self) -> impl Iterator<Item = &GlobalVar<Label>> {
        self.data.iter()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

impl<Label: Eq + Hash + Clone> GlobalVarMap<Label> {
    pub fn insert(&mut self, k: Label, v: GlobalVar<Label>) {
        self.data.push_back(v);
        let i = self.data.len() - 1;
        self.index.insert(k, i);
    }
    pub fn get<K: Hash + Eq>(&self, k: &K) -> Option<&GlobalVar<Label>>
    where
        Label: Borrow<K>,
    {
        let index = *self.index.get(k)?;
        self.data.get(index)
    }
    pub fn remove<K: Hash + Eq>(&mut self, k: &K) -> Option<()>
    where
        Label: Borrow<K>,
    {
        let index = self.index.remove(k)?;
        // indicate invalid
        self.data.get_mut(index).unwrap().size = 0;
        Some(())
    }
    pub fn contains_key(&self, k: &Label) -> bool {
        self.index.contains_key(k)
    }
    pub fn get_mut(&mut self, k: &Label) -> Option<&mut GlobalVar<Label>> {
        let index = *self.index.get(k)?;
        self.data.get_mut(index)
    }
}

impl<Label> Default for GlobalVarMap<Label> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
pub struct Asm<Ident, Label> {
    pub data_segment: DataSegment<Ident, Label>,
    pub text_segment: TextSegment<Label>,
    pub entry_point: Label,
}

#[derive(Debug, Clone)]
pub struct StaticLibrary<Label> {
    pub text_segment: TextSegment<Label>,
}

impl<Ident: Display, Label: Display> Display for Asm<Ident, Label> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for data_elem in &self.data_segment.other {
            use DataSegmentElem::*;
            match data_elem {
                Directive(d) => {
                    use DataSegmentDirective::*;
                    match d {
                        NextAlign(align) => writeln!(f, "\t.align {align}")?,
                        Labeled(lab) => writeln!(f, "{lab}:")?,
                    }
                }
                Data(d) => {
                    use DataKind::*;
                    match d {
                        Long(l) => writeln!(f, "\t.long {l:#010x}")?,
                        Array(a) => {
                            for l in a {
                                writeln!(f, "\t.long {l:#010x}")?;
                            }
                        }
                    }
                }
            }
        }
        for text_elem in self.text_segment.iter() {
            use TextSegmentElem::*;
            match text_elem {
                Directive(d) => {
                    use TextSegmentDirective::*;
                    match d {
                        NextAlign(align) => writeln!(f, "\t.align {align}")?,
                        Labeled(lab) => writeln!(f, "{lab}:")?,
                    }
                }
                Text(instr) => writeln!(f, "\t{instr}")?,
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct DataSegment<Ident, Label> {
    pub globals: GlobalVarMap<Ident>,
    pub other: Vec<DataSegmentElem<Label>>,
}

impl<Ident, Label> DataSegment<Ident, Label> {
    pub fn with_globals(globals: GlobalVarMap<Ident>, inner: Vec<DataSegmentElem<Label>>) -> Self {
        Self {
            globals,
            other: inner,
        }
    }
    pub fn new(inner: Vec<DataSegmentElem<Label>>) -> Self {
        Self {
            globals: GlobalVarMap::new(),
            other: inner,
        }
    }
    pub fn len(&self) -> usize {
        self.globals.values().map(|v| v.size).sum::<usize>() + self.other.len()
    }
    pub fn is_empty(&self) -> bool {
        self.globals.is_empty() && self.other.is_empty()
    }
}

#[derive(Debug, Clone)]
pub struct TextSegment<Label>(Vec<TextSegmentElem<Label>>);

impl<Label> TextSegment<Label> {
    pub fn new(inner: Vec<TextSegmentElem<Label>>) -> Self {
        Self(inner)
    }
    pub fn into_inner(self) -> Vec<TextSegmentElem<Label>> {
        self.0
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn instr(&mut self, i: Instr<Offset<Label>, Label>) {
        self.0.push(TextSegmentElem::Text(i))
    }
    pub fn label(&mut self, l: Label) {
        self.0
            .push(TextSegmentElem::Directive(TextSegmentDirective::Labeled(l)))
    }
    fn iter(&self) -> impl Iterator<Item = &TextSegmentElem<Label>> {
        self.0.iter()
    }
}

#[derive(Debug)]
pub enum DataSegmentElem<Label> {
    Directive(DataSegmentDirective<Label>),
    Data(DataKind),
}

#[derive(Debug)]
pub enum DataSegmentDirective<Label> {
    // base of 2
    NextAlign(u8),
    Labeled(Label),
}

#[derive(Debug)]
pub enum DataKind {
    // for float immediate
    Long(u32),
    Array(Vec<u32>),
}

#[derive(Debug, Clone)]
pub enum TextSegmentElem<Label> {
    Directive(TextSegmentDirective<Label>),
    Text(Instr<Offset<Label>, Label>),
}

#[derive(Debug, Clone)]
pub enum TextSegmentDirective<Label> {
    // base of 2
    NextAlign(u8),
    Labeled(Label),
}

#[derive(Debug, PartialEq, Clone)]
pub enum Offset<Label> {
    Label(Label),
    Const(Addr),
    Add(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
}

impl<Label: Display> Display for Offset<Label> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Offset::Label(l) => write!(f, "{l}"),
            Offset::Const(a) => write!(f, "0x{a:0X}"),
            Offset::Add(l, r) => write!(f, "({l} + {r})"),
            Offset::Sub(l, r) => write!(f, "({l} - {r})"),
        }
    }
}

impl<Label: Clone> Offset<Label> {
    fn resolve(&self, m: &impl RelocationTable<Label = Label>) -> Addr {
        match self {
            Offset::Label(l) => m.get_pcrel(l),
            Offset::Const(a) => *a,
            Offset::Add(l, r) => {
                let l = l.resolve(m);
                let r = r.resolve(m);
                l.wrapping_add(r)
            }
            Offset::Sub(l, r) => {
                let l = l.resolve(m);
                let r = r.resolve(m);
                l.wrapping_sub(r)
            }
        }
    }
    pub fn resolve_pcrel(&mut self, base: Addr, m: &impl RelocationTable<Label = Label>) {
        *self = Offset::Const(self.resolve(m).wrapping_sub(base))
    }
}

pub trait RelocationTable {
    type Label;
    fn get_zrel(&self, label: &Self::Label) -> Addr;
    fn get_pcrel(&self, label: &Self::Label) -> Addr;
}

pub type Addr = u32;

#[derive(Debug, PartialEq, Clone)]
pub enum Instr<Offset, Label> {
    Nullary(NullaryKind),
    Unary(UnaryKind, RegId),
    UnaryF(UnaryFKind, FRegId),
    UnaryOffset(UnaryOffsetKind, Offset),
    Binary(BinaryKind, RegId, RegId),
    BinaryF(BinaryFKind, FRegId, FRegId),
    BinaryIF(BinaryIFKind, RegId, FRegId),
    BinaryFI(BinaryFIKind, FRegId, RegId),
    BinaryImm(BinaryImmKind, RegId, i32),
    BinaryRegImm(BinaryRegImmKind, MemRegion, RegId, RegId, i32),
    TernaryRegLabelImm(BinaryRegImmKind, RegId, Option<RegId>, Label, i32),
    BinaryOffset(BinaryOffsetKind, RegId, Offset),
    BinaryFOffset(BinaryFOffsetKind, FRegId, Offset),
    BinaryLabel(BinaryLabelKind, RegId, Label),
    BinaryFLabel(BinaryFLabelKind, FRegId, Label),
    Ternary(TernaryKind, RegId, RegId, RegId),
    TernaryImm(TernaryImmKind, RegId, RegId, i32),
    TernaryF(TernaryFKind, FRegId, FRegId, FRegId),
    TernaryIF(TernaryIFKind, RegId, FRegId, FRegId),
    BinaryFRegImm(BinaryFRegImmKind, MemRegion, FRegId, RegId, i32),
    TernaryFRegLabelImm(BinaryFRegImmKind, FRegId, Option<RegId>, Label, i32),
    TernaryOffset(TernaryOffsetKind, RegId, RegId, Offset),
    #[cfg(feature = "isa_2nd")]
    TernaryImm2Offset(TernaryImm2OffsetKind, RegId, i32, Offset),
    TernaryFOffset(TernaryFOffsetKind, FRegId, FRegId, Offset),
    #[cfg(feature = "isa_2nd")]
    QuaternaryF(QuaternaryFKind, FRegId, FRegId, FRegId, FRegId),
}

impl<Offset: Display, Label: Display> Display for Instr<Offset, Label> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Instr::*;
        match self {
            Nullary(k) => write!(f, "{k}"),
            Unary(k, a1) => write!(f, "{k} {a1}"),
            UnaryF(k, a1) => write!(f, "{k} {a1}"),
            UnaryOffset(k, a1) => write!(f, "{k} {a1}"),
            Binary(k, a1, a2) => write!(f, "{k} {a1}, {a2}"),
            BinaryF(k, a1, a2) => write!(f, "{k} {a1}, {a2}"),
            BinaryIF(k, a1, a2) => write!(f, "{k} {a1}, {a2}"),
            BinaryFI(k, a1, a2) => write!(f, "{k} {a1}, {a2}"),
            BinaryImm(k, a1, a2) => write!(f, "{k} {a1}, {a2}"),
            BinaryRegImm(k, k2, a1, a2, imm) => write!(f, "{k}{k2} {a1}, {imm}({a2})"),
            TernaryRegLabelImm(k, a1, None, a2, imm) => write!(f, "{k} {a1}, {imm}({a2})"),
            TernaryRegLabelImm(k, a1, Some(a2), a3, imm) => {
                write!(f, "{k} {a1}, {imm}({a2} + {a3})")
            }
            BinaryOffset(k, a1, a2) => write!(f, "{k} {a1}, {a2}"),
            BinaryFOffset(k, a1, a2) => write!(f, "{k} {a1}, {a2}"),
            BinaryLabel(k, a1, a2) => write!(f, "{k} {a1}, {a2}"),
            BinaryFLabel(k, a1, a2) => write!(f, "{k} {a1}, {a2}"),
            Ternary(k, a1, a2, a3) => write!(f, "{k} {a1}, {a2}, {a3}"),
            TernaryImm(k, a1, a2, a3) => write!(f, "{k} {a1}, {a2}, {a3}"),
            TernaryF(k, a1, a2, a3) => write!(f, "{k} {a1}, {a2}, {a3}"),
            TernaryIF(k, a1, a2, a3) => write!(f, "{k} {a1}, {a2}, {a3}"),
            BinaryFRegImm(k, k2, a1, a2, imm) => write!(f, "{k}{k2} {a1}, {imm}({a2})"),
            TernaryFRegLabelImm(k, a1, None, a2, imm) => write!(f, "{k} {a1}, {imm}({a2})"),
            TernaryFRegLabelImm(k, a1, Some(a2), a3, imm) => {
                write!(f, "{k} {a1}, {imm}({a2} + {a3})")
            }
            TernaryOffset(k, a1, a2, a3) => write!(f, "{k} {a1}, {a2}, {a3}"),
            #[cfg(feature = "isa_2nd")]
            TernaryImm2Offset(k, a1, a2, a3) => write!(f, "{k} {a1}, {a2}, {a3}"),
            TernaryFOffset(k, a1, a2, a3) => write!(f, "{k} {a1}, {a2}, {a3}"),
            #[cfg(feature = "isa_2nd")]
            QuaternaryF(k, a1, a2, a3, a4) => write!(f, "{k} {a1}, {a2}, {a3}, {a4}"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum NullaryKind {
    Nop,
    Ret,
    End,
}

impl Display for NullaryKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            NullaryKind::Nop => "nop",
            NullaryKind::Ret => "ret",
            NullaryKind::End => "end",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum UnaryKind {
    Jr,
    Jalr,
    Inw,
    Outb,
}

impl Display for UnaryKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            UnaryKind::Jr => "jr",
            UnaryKind::Jalr => "jalr",
            UnaryKind::Inw => "inw",
            UnaryKind::Outb => "outb",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum UnaryFKind {
    Finw,
}

impl Display for UnaryFKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("finw")
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum UnaryOffsetKind {
    J,
    Jal,
}

impl Display for UnaryOffsetKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            UnaryOffsetKind::J => "j",
            UnaryOffsetKind::Jal => "jal",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryKind {
    Mv,
    Not,
    #[cfg(not(feature = "isa_2nd"))]
    Neg,
}

impl Display for BinaryKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            BinaryKind::Mv => "mv",
            BinaryKind::Not => "not",
            #[cfg(not(feature = "isa_2nd"))]
            BinaryKind::Neg => "neg",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryFKind {
    Fmv,
    Fneg,
    Fhalf,
    Fabs,
    Fsqrt,
    Ffloor,
    Finv,
}

impl Display for BinaryFKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            BinaryFKind::Fmv => "fmv",
            BinaryFKind::Fneg => "fneg",
            BinaryFKind::Fhalf => "fhalf",
            BinaryFKind::Fabs => "fabs",
            BinaryFKind::Fsqrt => "sqrt",
            BinaryFKind::Ffloor => "floor",
            BinaryFKind::Finv => "finv",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryIFKind {
    Fftoi,
    Fiszero,
    Fispos,
    Fisneg,
}

impl Display for BinaryIFKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            BinaryIFKind::Fftoi => "fftoi",
            BinaryIFKind::Fiszero => "fiszero",
            BinaryIFKind::Fispos => "fispos",
            BinaryIFKind::Fisneg => "fisneg",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryFIKind {
    Fitof,
}

impl Display for BinaryFIKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            BinaryFIKind::Fitof => "fitof",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryImmKind {
    Li,
}

impl Display for BinaryImmKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("li")
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryOffsetKind {
    Beqz,
    Bnez,
    Bltz,
    Blez,
    Bgtz,
    Bgez,
}

impl Display for BinaryOffsetKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            BinaryOffsetKind::Beqz => "beqz",
            BinaryOffsetKind::Bnez => "bnez",
            BinaryOffsetKind::Bltz => "bltz",
            BinaryOffsetKind::Blez => "blez",
            BinaryOffsetKind::Bgtz => "bgtz",
            BinaryOffsetKind::Bgez => "bgez",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryFOffsetKind {
    Fbeqz,
    Fbnez,
    Fbltz,
    Fblez,
    Fbgtz,
    Fbgez,
}

impl Display for BinaryFOffsetKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            BinaryFOffsetKind::Fbeqz => "fbeqz",
            BinaryFOffsetKind::Fbnez => "fbnez",
            BinaryFOffsetKind::Fbltz => "fbltz",
            BinaryFOffsetKind::Fblez => "fblez",
            BinaryFOffsetKind::Fbgtz => "fbgtz",
            BinaryFOffsetKind::Fbgez => "fbgez",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryLabelKind {
    LoadLabelAddr,
    LoadFromLabel,
}

impl Display for BinaryLabelKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            BinaryLabelKind::LoadLabelAddr => "mv",
            BinaryLabelKind::LoadFromLabel => "lw",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryFLabelKind {
    FLoadFromLabel,
}

impl Display for BinaryFLabelKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("flw")
    }
}

cfg_if::cfg_if! {
    if #[cfg(feature = "isa_2nd")] {
        #[derive(Debug, PartialEq, Clone)]
        pub enum TernaryKind {
            Add,
            Xor,
            Min,
            Max,
        }

        impl Display for TernaryKind {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let s = match self {
                    TernaryKind::Add => "add",
                    TernaryKind::Xor => "xor",
                    TernaryKind::Min => "min",
                    TernaryKind::Max => "max",
                };
                f.write_str(s)
            }
        }
    } else {
        #[derive(Debug, PartialEq, Clone)]
        pub enum TernaryKind {
            Add,
            Sub,
            Xor,
            Or,
            And,
            Sll,
            Sra,
            Slt,
        }

        impl Display for TernaryKind {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let s = match self {
                    TernaryKind::Add => "add",
                    TernaryKind::Sub => "sub",
                    TernaryKind::Xor => "xor",
                    TernaryKind::Or => "or",
                    TernaryKind::And => "and",
                    TernaryKind::Sll => "sll",
                    TernaryKind::Sra => "sra",
                    TernaryKind::Slt => "slt",
                };
                f.write_str(s)
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TernaryFKind {
    Fadd,
    Fsub,
    Fmul,
    Fdiv,
    Fsgnj,
    Fsgnjn,
    Fsgnjx,
}

impl Display for TernaryFKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            TernaryFKind::Fadd => "fadd",
            TernaryFKind::Fsub => "fsub",
            TernaryFKind::Fmul => "fmul",
            TernaryFKind::Fdiv => "fdiv",
            TernaryFKind::Fsgnj => "fsgnj",
            TernaryFKind::Fsgnjn => "fsgnjn",
            TernaryFKind::Fsgnjx => "fsgnjx",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TernaryIFKind {
    Flt,
}

impl Display for TernaryIFKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            TernaryIFKind::Flt => "flt",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryRegImmKind {
    Sw,
    Lw,
}

impl Display for BinaryRegImmKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            BinaryRegImmKind::Sw => "sw",
            BinaryRegImmKind::Lw => "lw",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone, Default)]
pub enum MemRegion {
    Data,
    #[default]
    Heap,
    Stack,
}

impl MemRegion {
    pub fn f3(&self) -> u32 {
        match self {
            MemRegion::Data => 0b001,
            MemRegion::Heap => 0b010,
            MemRegion::Stack => 0b100,
        }
    }
}

impl Display for MemRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            MemRegion::Data => "d",
            MemRegion::Heap => "h",
            MemRegion::Stack => "s",
        };
        f.write_str(s)
    }
}

cfg_if::cfg_if! {
    if #[cfg(feature = "isa_2nd")] {
        #[derive(Debug, PartialEq, Clone)]
        pub enum TernaryImmKind {
            Addi,
            Subi,
            Xori,
            Slli,
        }

        impl Display for TernaryImmKind {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let s = match self {
                    TernaryImmKind::Addi => "addi",
                    TernaryImmKind::Subi => "subi",
                    TernaryImmKind::Xori => "xori",
                    TernaryImmKind::Slli => "slli",
                };
                f.write_str(s)
            }
        }
    }
    else {
        #[derive(Debug, PartialEq, Clone)]
        pub enum TernaryImmKind {
            Addi,
            Subi,
            Xori,
            Ori,
            Andi,
            Slli,
            Srai,
            Slti,
        }

        impl Display for TernaryImmKind {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let s = match self {
                    TernaryImmKind::Addi => "addi",
                    TernaryImmKind::Subi => "subi",
                    TernaryImmKind::Xori => "xori",
                    TernaryImmKind::Ori => "ori",
                    TernaryImmKind::Andi => "andi",
                    TernaryImmKind::Slli => "slli",
                    TernaryImmKind::Srai => "srai",
                    TernaryImmKind::Slti => "slti",
                };
                f.write_str(s)
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum BinaryFRegImmKind {
    Fsw,
    Flw,
}

impl Display for BinaryFRegImmKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            BinaryFRegImmKind::Fsw => "fsw",
            BinaryFRegImmKind::Flw => "flw",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TernaryOffsetKind {
    Beq,
    Bne,
    Blt,
    Ble,
    Bgt,
    Bge,
    #[cfg(feature = "isa_2nd")]
    Bxor,
    #[cfg(feature = "isa_2nd")]
    Bxnor,
}

impl Display for TernaryOffsetKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            TernaryOffsetKind::Beq => "beq",
            TernaryOffsetKind::Bne => "bne",
            TernaryOffsetKind::Blt => "blt",
            TernaryOffsetKind::Ble => "ble",
            TernaryOffsetKind::Bgt => "bgt",
            TernaryOffsetKind::Bge => "bge",
            #[cfg(feature = "isa_2nd")]
            TernaryOffsetKind::Bxor => "bxor",
            #[cfg(feature = "isa_2nd")]
            TernaryOffsetKind::Bxnor => "bxnor",
        };
        f.write_str(s)
    }
}

#[cfg(feature = "isa_2nd")]
#[derive(Debug, PartialEq, Clone)]
pub enum TernaryImm2OffsetKind {
    Beqi,
    Bnei,
    Blti,
    Blei,
    Bgti,
    Bgei,
}

#[cfg(feature = "isa_2nd")]
impl Display for TernaryImm2OffsetKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            TernaryImm2OffsetKind::Beqi => "beqi",
            TernaryImm2OffsetKind::Bnei => "bnei",
            TernaryImm2OffsetKind::Blti => "blti",
            TernaryImm2OffsetKind::Blei => "blei",
            TernaryImm2OffsetKind::Bgti => "bgti",
            TernaryImm2OffsetKind::Bgei => "bgei",
        };
        f.write_str(s)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TernaryFOffsetKind {
    Fblt,
    Fble,
    Fbgt,
    Fbge,
}

impl Display for TernaryFOffsetKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            TernaryFOffsetKind::Fblt => "fblt",
            TernaryFOffsetKind::Fble => "fble",
            TernaryFOffsetKind::Fbgt => "fbgt",
            TernaryFOffsetKind::Fbge => "fbge",
        };
        f.write_str(s)
    }
}

#[cfg(feature = "isa_2nd")]
#[derive(Debug, PartialEq, Clone)]
pub enum QuaternaryFKind {
    Fmadd,
    Fmsub,
    Fnmadd,
    Fnmsub,
}

#[cfg(feature = "isa_2nd")]
impl Display for QuaternaryFKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            QuaternaryFKind::Fmadd => "fmadd",
            QuaternaryFKind::Fmsub => "fmsub",
            QuaternaryFKind::Fnmadd => "fnmadd",
            QuaternaryFKind::Fnmsub => "fnmsub",
        };
        f.write_str(s)
    }
}

#[macro_export]
macro_rules! pseudo {
    ($i:ident) => {
        Instr::Nullary(NullaryKind::$i)
    };
}

#[macro_export]
macro_rules! pseudo_i {
    ($i:ident $rd:tt) => {
        Instr::Unary(UnaryKind::$i, $rd)
    };
    ($i:ident # $off:tt) => {
        Instr::UnaryOffset(UnaryOffsetKind::$i, $off)
    };
    ($i:ident $rd:tt, $rs1:tt) => {
        Instr::Binary(BinaryKind::$i, $rd, $rs1)
    };
    ($i:ident $rd:tt, imm: $imm:tt) => {
        Instr::BinaryImm(BinaryImmKind::$i, $rd, $imm)
    };
    ($i:ident $rd:tt, # $off:tt) => {
        Instr::BinaryOffset(BinaryOffsetKind::$i, $rd, $off)
    };
    ($i:ident $rd:tt, .$l:tt) => {
        Instr::BinaryLabel(BinaryLabelKind::$i, $rd, $l)
    };
    ($i:ident $rd:tt, $rs1:tt, $rs2:tt) => {
        Instr::Ternary(TernaryKind::$i, $rd, $rs1, $rs2)
    };
    ($i:ident $rd:tt, $rs1:tt, imm: $imm:tt) => {
        Instr::TernaryImm(TernaryImmKind::$i, $rd, $rs1, $imm)
    };
    ($i:ident[$loc:tt] $rd:tt, $imm:tt($rs1:tt)) => {
        Instr::BinaryRegImm(BinaryRegImmKind::$i, memloc!($loc), $rd, $rs1, $imm)
    };
    ($i:ident $rd:tt, $imm:tt(.$l:tt + $rs1:tt)) => {
        Instr::TernaryRegLabelImm(BinaryRegImmKind::$i, $rd, $rs1, $l, $imm)
    };
    ($i:ident $rd:tt, $rs1:tt, # $off:tt) => {
        Instr::TernaryOffset(TernaryOffsetKind::$i, $rd, $rs1, $off)
    };
    ($i:ident $rd:tt, imm: $imm:tt, # $off:tt) => {
        Instr::TernaryImm2Offset(TernaryImm2OffsetKind::$i, $rd, $imm, $off)
    };
}

#[macro_export]
macro_rules! pseudo_f {
    ($i:ident $rd:tt) => {
        Instr::UnaryF(UnaryFKind::$i, $rd)
    };
    ($i:ident # $off:tt) => {
        Instr::UnaryFOffset(UnaryFOffsetKind::$i, $off)
    };
    ($i:ident $rd:tt, $rs1:tt) => {
        Instr::BinaryF(BinaryFKind::$i, $rd, $rs1)
    };
    ($i:ident $rd:tt, imm: $imm:tt) => {
        Instr::BinaryFImm(BinaryFImmKind::$i, $rd, $imm)
    };
    ($i:ident $rd:tt, # $off:tt) => {
        Instr::BinaryFOffset(BinaryFOffsetKind::$i, $rd, $off)
    };
    ($i:ident $rd:tt, .$l:tt) => {
        Instr::BinaryFLabel(BinaryFLabelKind::$i, $rd, $l)
    };
    ($i:ident $rd:tt, $rs1:tt, $rs2:tt) => {
        Instr::TernaryF(TernaryFKind::$i, $rd, $rs1, $rs2)
    };
    ($i:ident[$loc:tt] $rd:tt, $imm:tt($rs1:tt)) => {
        Instr::BinaryFRegImm(BinaryFRegImmKind::$i, memloc!($loc), $rd, $rs1, $imm)
    };
    ($i:ident $rd:tt, $imm:tt(.$l:tt + $rs1:tt)) => {
        Instr::TernaryFRegLabelImm(BinaryFRegImmKind::$i, $rd, $rs1, $l, $imm)
    };
    ($i:ident $rd:tt, $rs1:tt, # $off:tt) => {
        Instr::TernaryFOffset(TernaryFOffsetKind::$i, $rd, $rs1, $off)
    };
    ($i:ident $rd:tt, $rs1:tt, $rs2:tt, $rs3:tt) => {
        Instr::QuaternaryF(QuaternaryFKind::$i, $rd, $rs1, $rs2, $rs3)
    };
}

#[macro_export]
macro_rules! pseudo_misc {
    ($i:ident x[$rd:tt], f[$rs1:tt]) => {
        Instr::BinaryIF(BinaryIFKind::$i, $rd, $rs1)
    };
    ($i:ident x[$rd:tt], f[$rs1:tt], f[$rs2:tt]) => {
        Instr::TernaryIF(TernaryIFKind::$i, $rd, $rs1, $rs2)
    };
    ($i:ident f[$rd:tt], x[$rs1:tt]) => {
        Instr::BinaryFI(BinaryFIKind::$i, $rd, $rs1)
    };
}

#[macro_export]
macro_rules! memloc {
    (d) => {
        MemRegion::Data
    };
    (h) => {
        MemRegion::Heap
    };
    (s) => {
        MemRegion::Stack
    };
    ($i:ident) => {
        $i
    };
}
