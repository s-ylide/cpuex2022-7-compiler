//! this module is the "assembler" and "linker"
#![feature(option_get_or_insert_default)]

mod bit;
mod encode_instr;
mod format;
mod instr;
use instr::*;

use debug_symbol::{DebugSymbol, SymbolDef};
use std::{cell::RefCell, collections::HashMap, fmt::Display, hash::Hash, rc::Rc};
use typedefs::{Ident, Label};

use bit::*;
use ir_asm_ast_isa1st::{
    abi::{FRegId, RegId, REG_X0},
    *,
};
use smallvec::{smallvec, SmallVec};

/// assemble and link the program.
pub fn assemble_and_link<'a>(
    mut asm: Asm<Ident<'a>, Label<'a>>,
    lib: Option<StaticLibrary<Label<'a>>>,
    debug_symbol: &mut DebugSymbol,
) -> Vec<u8> {
    /// imitating an line of object file that aren't linked yet,
    /// without offset information
    enum ObjectAlignment<Offset> {
        Padding(u32),
        ToBeEncodedInstr(BaseInstr<Offset>),
        Data(DataKind),
    }

    let mut st = LinkerState {
        relocation_table_pcrel: HashMap::new(),
        relocation_table_zrel: HashMap::new(),
    };
    // decide alignment of .text and .data before link offsets
    let mut alignment = Vec::with_capacity(asm.data_segment.len() * 4 + asm.text_segment.len() * 4);
    let mut addr: Addr;
    macro_rules! padding {
        ($align:expr) => {
            let excess = addr % $align;
            if excess != 0 {
                let pad = $align - excess;
                addr += pad;
                alignment.push(ObjectAlignment::Padding(pad));
            }
        };
    }
    let data_begin_addr = 0x0;
    let data_segment_len = {
        addr = data_begin_addr;
        let mut next_align = None;
        let mut current_label: Option<Vec<_>> = None;
        {
            use DataKind::*;
            let mut addr_map = HashMap::with_capacity(asm.data_segment.globals.data.len());
            while let Some(d) = asm.data_segment.globals.data.pop_front() {
                if d.value
                    .as_cconst()
                    .iter()
                    .flat_map(|c| c.as_address_of())
                    .any(|l| !addr_map.contains_key(l))
                {
                    // calculate this later
                    asm.data_segment.globals.data.push_back(d);
                    continue;
                }
                let GlobalVar {
                    name, size, value, ..
                } = d;
                if size == 0 {
                    continue;
                }
                st.relocation_table_zrel
                    .insert(Label::from(name.clone()), addr - data_begin_addr);
                addr_map.insert(name, addr);
                use CompileTimeConst::*;
                use GlobalVarValue::*;

                fn get_const<Ident: Hash + Eq>(
                    c: CompileTimeConst<Ident>,
                    addr_map: &HashMap<Ident, u32>,
                ) -> u32 {
                    match c {
                        AddressOf(l) => *addr_map.get(&l).unwrap(),
                        Int(i) => i as u32,
                        Float(f) => f.to_bits(),
                    }
                }

                match value {
                    Array(GlobalVarArray {
                        count,
                        data,
                        modification,
                    }) => {
                        let mut a = vec![get_const(data, &addr_map); count as usize];
                        if !modification.is_empty() {
                            for (index, value) in modification.into_iter() {
                                a[index as usize] = get_const(value, &addr_map);
                            }
                        }
                        alignment.push(ObjectAlignment::Data(DataKind::Array(a)));
                    }
                    EmptyArray => todo!("this will have been folded into 0"),
                    Tuple(t) => {
                        for c in t {
                            alignment.push(ObjectAlignment::Data(Long(get_const(c, &addr_map))));
                        }
                    }
                    Const(c) => {
                        alignment.push(ObjectAlignment::Data(Long(get_const(c, &addr_map))));
                    }
                }

                addr += (size >> 2) as u32;
            }
        }
        for line in asm.data_segment.other {
            use DataSegmentDirective::*;
            use DataSegmentElem::*;
            match line {
                Directive(NextAlign(a)) => next_align = Some((a >> 2) as u32),
                Directive(Labeled(l)) => current_label.get_or_insert_default().push(l),
                Data(data) => {
                    use ObjectAlignment::*;
                    // padding
                    if let Some(align) = next_align.take() {
                        padding!(align);
                    }
                    // labelling
                    if let Some(labels) = current_label.take() {
                        for label in labels {
                            st.relocation_table_zrel
                                .insert(label, addr - data_begin_addr);
                        }
                    }
                    match &data {
                        DataKind::Long(_) => {
                            addr += 1;
                        }
                        DataKind::Array(a) => {
                            addr += a.len() as u32;
                        }
                    };
                    alignment.push(Data(data));
                }
            }
        }
        addr - data_begin_addr
    };
    let mut unresolved_pcrel_offsets = Vec::new();
    let text_segment_len = {
        let begin_addr = data_begin_addr + data_segment_len;
        addr = begin_addr;
        let mut next_align = None;
        let mut current_label: Option<Vec<_>> = None;
        for line in [
            TextSegmentElem::Directive(TextSegmentDirective::Labeled(Label::name("startup"))),
            TextSegmentElem::Text({
                let offset = Offset::Label(asm.entry_point);
                pseudo_i!(J #offset)
            }),
        ]
        .into_iter()
        .chain(lib.into_iter().flat_map(|l| l.text_segment.into_inner()))
        .chain(asm.text_segment.into_inner().into_iter())
        {
            use ObjectAlignment::*;
            use TextSegmentDirective::*;
            use TextSegmentElem::*;
            match line {
                Directive(NextAlign(a)) => next_align = Some((a >> 2) as u32),
                Directive(Labeled(l)) => current_label.get_or_insert_default().push(l),
                Text(instr) => {
                    // padding
                    if let Some(align) = next_align.take() {
                        padding!(align);
                    }
                    // labelling
                    if let Some(labels) = current_label.take() {
                        for label in labels {
                            st.relocation_table_pcrel.insert(label, addr << 2);
                        }
                    }
                    let reals = desugar_instr(instr, &st);
                    unresolved_pcrel_offsets.extend(
                        reals
                            .iter()
                            .flat_map(BaseInstr::as_pcrel_offset)
                            // addr points to reals[0], for auipc + jalr
                            .map(|rc| (addr << 2, rc.clone())),
                    );
                    alignment.extend(
                        reals
                            .into_iter()
                            .inspect(|_| addr += 1)
                            .map(ToBeEncodedInstr),
                    );
                }
            };
        }
        addr - begin_addr
    };

    debug_symbol
        .globals
        .extend(st.relocation_table_zrel.iter().map(|(l, &addr)| SymbolDef {
            label: l.to_inner_string(),
            addr,
        }));
    debug_symbol.labels.extend(
        st.relocation_table_pcrel
            .iter()
            .map(|(l, &addr)| SymbolDef {
                label: l.to_unique_string(),
                addr,
            }),
    );

    // then link offsets
    for (addr, unresolved_offset) in unresolved_pcrel_offsets {
        let mut off = unresolved_offset.borrow_mut();
        let value = off.get_mut();
        value.resolve_pcrel(addr, &st);
    }
    // finally put all things to byte array
    let total_len = (2 + data_segment_len + text_segment_len) << 2;
    let mut bin = Vec::with_capacity(total_len as usize);
    // 0:3
    bin.extend_from_slice(&data_segment_len.to_le_bytes());
    // 4:7
    bin.extend_from_slice(&text_segment_len.to_le_bytes());
    // 8:
    for obj in alignment {
        use ObjectAlignment::*;
        match obj {
            Padding(pad) => {
                bin.append(&mut vec![0xcc; (pad << 2) as usize]);
            }
            ToBeEncodedInstr(instr) => {
                let u32 = instr.encode();
                bin.extend_from_slice(&u32.to_le_bytes());
            }
            Data(data) => match data {
                DataKind::Long(l) => {
                    bin.extend_from_slice(&l.to_le_bytes());
                }
                DataKind::Array(a) => {
                    bin.extend(a.into_iter().flat_map(u32::to_le_bytes));
                }
            },
        }
    }
    bin
}

pub trait AsConst {
    type Const;
    fn as_const(&self) -> Option<Self::Const>;
}

impl AsConst for Addr {
    type Const = Self;

    fn as_const(&self) -> Option<Self::Const> {
        Some(*self)
    }
}

impl<T: AsConst> AsConst for Rc<RefCell<T>> {
    type Const = T::Const;

    fn as_const(&self) -> Option<Self::Const> {
        self.borrow().as_const()
    }
}

impl<Label> AsConst for Offset<Label> {
    type Const = Addr;

    fn as_const(&self) -> Option<Addr> {
        use Offset::*;
        match self {
            Const(c) => Some(*c),
            _ => None,
        }
    }
}

impl<O> BaseInstr<O> {
    pub fn as_pcrel_offset(&self) -> Option<&O> {
        use BaseInstr::*;
        use FInstr::*;
        match self {
            B { imm, .. } | J { imm, .. } | F(W { imm, .. }) | F(V { imm, .. }) => Some(imm),
            #[cfg(feature = "isa_2nd")]
            P { imm, .. } => Some(imm),
            _ => None,
        }
    }
}

#[derive(Debug)]
struct LinkerState<Label> {
    relocation_table_pcrel: HashMap<Label, Addr>,
    relocation_table_zrel: HashMap<Label, Addr>,
}

impl<Label: Eq + Hash + Display> RelocationTable for LinkerState<Label> {
    type Label = Label;
    fn get_zrel(&self, label: &Label) -> Addr {
        *self
            .relocation_table_zrel
            .get(label)
            .unwrap_or_else(|| panic!("label {label} should be in relocation table"))
    }
    fn get_pcrel(&self, label: &Label) -> Addr {
        *self.relocation_table_pcrel.get(label).unwrap_or_else(|| {
            panic!(
                "label {label} should be in relocation table, meaning there should be no unlinked offset"
            )
        })
    }
}

#[derive(PartialEq, Eq)]
enum LinkerOpKind {
    /// expr[31:12], cancells out sign extension
    ExcessIImm,
    Pass,
}

struct LinkerExpr<T> {
    operation: LinkerOpKind,
    value: T,
}

impl<T> LinkerExpr<T> {
    pub fn hi_u(value: T) -> Self {
        Self {
            operation: LinkerOpKind::ExcessIImm,
            value,
        }
    }
    pub fn pass(value: T) -> Self {
        Self {
            operation: LinkerOpKind::Pass,
            value,
        }
    }
    pub fn get_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<Offset: AsConst<Const = Addr>> AsConst for LinkerExpr<Offset> {
    type Const = Addr;
    fn as_const(&self) -> Option<Self::Const> {
        use LinkerOpKind::*;
        let c = self.value.as_const()?;
        Some(match self.operation {
            ExcessIImm => {
                let u = get_hi(c);
                let sign_extends = at(c, 11) != 0;
                if sign_extends {
                    let u = u.wrapping_sub(bit_range_lower(19));
                    mask_lower(u, 19)
                } else {
                    u
                }
            }
            Pass => c,
        })
    }
}

#[inline]
fn get_hi(bin: u32) -> u32 {
    extract(bin, 12..31)
}

macro_rules! reg {
    ($l:literal) => {
        RegId::new($l)
    };
    ($i:ident) => {
        $i
    };
}

macro_rules! freg {
    ($l:literal) => {
        FRegId::new($l)
    };
    ($i:ident) => {
        $i
    };
}

macro_rules! ofs {
    ($i:ident) => {
        LinkerExpr::pass($i)
    };
    (%hi $i:ident) => {
        LinkerExpr::hi($i)
    };
    (%lo $i:ident) => {
        LinkerExpr::lo($i)
    };
}

macro_rules! instr {
    (Misc: $i:ident) => {
        BaseInstr::Misc {
            instr: MiscInstr::$i,
        }
    };
    (R : $i:ident $rd:tt, $rs1:tt, $rs2:tt) => {
        BaseInstr::R {
            instr: RInstr::$i,
            rd: reg!($rd),
            rs1: reg!($rs1),
            rs2: reg!($rs2),
        }
    };
    (Lw[$loc:tt] $rd:tt, $imm:tt($rs1:tt)) => {
        BaseInstr::I {
            instr: IInstr::Lw(memloc!($loc)),
            rd: reg!($rd),
            rs1: reg!($rs1),
            imm: $imm as u32,
        }
    };
    (I : $i:ident $rd:tt, $rs1:tt, $imm:expr) => {
        BaseInstr::I {
            instr: IInstr::$i,
            rd: reg!($rd),
            rs1: reg!($rs1),
            imm: $imm as u32,
        }
    };
    (I : $i:ident $rd:tt, $rs1:tt, $($ofs:tt)*) => {
        BaseInstr::IPcOffset {
            instr: IInstr::$i,
            rd: reg!($rd),
            rs1: reg!($rs1),
            imm: Rc::new(RefCell::new(ofs!($($ofs)*))),
        }
    };
    (Sw[$loc:tt] $rs2:tt, $imm:tt($rs1:tt)) => {
        BaseInstr::S {
            instr: SInstr::Sw(memloc!($loc)),
            rs1: reg!($rs1),
            rs2: reg!($rs2),
            imm: $imm as u32,
        }
    };
    (B : $i:ident $rs1:tt, $rs2:tt, $($ofs:tt)*) => {
        BaseInstr::B {
            instr: BInstr::$i,
            rs1: reg!($rs1),
            rs2: reg!($rs2),
            imm: Rc::new(RefCell::new(ofs!($($ofs)*))),
        }
    };
    (P : $i:ident $rs1:tt, $imm:tt, $($ofs:tt)*) => {
        BaseInstr::P {
            instr: PInstr::$i,
            rs1: reg!($rs1),
            imm: Rc::new(RefCell::new(ofs!($($ofs)*))),
            imm2: $imm as u32,
        }
    };
    (J : $i:ident $rd:tt, $ofs:tt) => {
        BaseInstr::J {
            instr: JInstr::$i,
            rd: reg!($rd),
            imm: Rc::new(RefCell::new(ofs!($ofs))),
        }
    };
    (U : $i:ident $rd:tt, $imm:expr) => {
        BaseInstr::U {
            instr: UInstr::$i,
            rd: reg!($rd),
            imm: $imm,
        }
    };
    (U : $i:ident $rd:tt, %hi $o:ident) => {
        BaseInstr::UPcOffset {
            instr: UInstr::$i,
            rd: reg!($rd),
            imm: Rc::new(RefCell::new(LinkerExpr::hi_u($o))),
        }
    };
    (F.W : $i:ident $rs1:tt, $rs2:tt, $($ofs:tt)*) => {
        BaseInstr::F(FInstr::W {
            instr: WInstr::$i,
            rs1: freg!($rs1),
            rs2: freg!($rs2),
            imm: Rc::new(RefCell::new(ofs!($($ofs)*))),
        })
    };
    (F.V : $i:ident $rs1:tt, $($ofs:tt)*) => {
        BaseInstr::F(FInstr::V {
            instr: VInstr::$i,
            rs1: freg!($rs1),
            imm: Rc::new(RefCell::new(ofs!($($ofs)*))),
        })
    };
    (Flw[$loc:tt] $rd:tt, $imm:tt($rs1:tt)) => {
        BaseInstr::F(FInstr::Flw { region: memloc!($loc), rd: $rd, rs1: $rs1, imm: $imm as u32 })
    };
    (Fsw[$loc:tt] $rs2:tt, $imm:tt($rs1:tt)) => {
        BaseInstr::F(FInstr::Fsw { region: memloc!($loc), rs2: $rs2, rs1: $rs1, imm: $imm as u32 })
    };
    (F.E : $i:ident $rd:tt, $rs1:tt, $rs2:tt) => {
        BaseInstr::F(FInstr::E {
            instr: EInstr::$i,
            rd: freg!($rd),
            rs1: freg!($rs1),
            rs2: freg!($rs2),
        })
    };
    (F.G : $i:ident $rd:tt, $rs1:tt, $rs2:tt, $rs3:tt) => {
        BaseInstr::F(FInstr::G {
            instr: GInstr::$i,
            rd: freg!($rd),
            rs1: freg!($rs1),
            rs2: freg!($rs2),
            rs3: freg!($rs3),
        })
    };
    (F.K : $i:ident $rd:tt, $rs1:tt, $rs2:tt) => {
        BaseInstr::F(FInstr::K {
            instr: KInstr::$i,
            rd: reg!($rd),
            rs1: freg!($rs1),
            rs2: freg!($rs2),
        })
    };
    (F.H : $i:ident $rd:tt, $rs1:tt) => {
        BaseInstr::F(FInstr::H {
            instr: HInstr::$i,
            rd: freg!($rd),
            rs1: freg!($rs1),
        })
    };
    (F.X : $i:ident $rd:tt, $rs1:tt) => {
        BaseInstr::F(FInstr::X {
            instr: XInstr::$i,
            rd: freg!($rd),
            rs1: reg!($rs1),
        })
    };
    (F.Y : $i:ident $rd:tt, $rs1:tt) => {
        BaseInstr::F(FInstr::Y {
            instr: YInstr::$i,
            rd: reg!($rd),
            rs1: freg!($rs1),
        })
    };
    (IO : $i:ident $tt:ident) => {
        BaseInstr::IO(IOInstr::$i { $tt })
    };
}

trait FromConst {
    type Const;
    fn from_const(c: Self::Const) -> Self;
}

impl<L> FromConst for Offset<L> {
    type Const = Addr;

    fn from_const(c: Addr) -> Self {
        Offset::Const(c)
    }
}

type BaseInstrs<Offset> = SmallVec<[BaseInstr<Rc<RefCell<LinkerExpr<Offset>>>>; 2]>;

fn desugar_instr<Label: Eq + Hash + Display, Offset: Clone + FromConst<Const = Addr>>(
    instr: Instr<Offset, Label>,
    st: &LinkerState<Label>,
) -> BaseInstrs<Offset> {
    let instr = match instr {
        // pseudo instructions
        pseudo_i!(LoadLabelAddr rd, .symbol) => {
            let imm = st.get_zrel(&symbol);
            instr!(I: Addi rd, REG_X0, imm)
        }
        pseudo_i!(LoadFromLabel rd, .symbol) => {
            let imm = st.get_zrel(&symbol);
            assert!(within(imm, 10));
            instr!(Lw[d] rd, imm(REG_X0))
        }
        pseudo_f!(FLoadFromLabel rd, .symbol) => {
            let imm = st.get_zrel(&symbol);
            assert!(within(imm, 10));
            instr!(Flw[d] rd, imm(REG_X0))
        }
        pseudo_i!(Lw rd, imm(.symbol + rs1)) => {
            let rs1 = rs1.unwrap_or(REG_X0);
            let symbol = st.get_zrel(&symbol);
            let imm = symbol + imm as u32;
            assert!(within(imm, 10));
            instr!(Lw[d] rd, imm(rs1))
        }
        pseudo_f!(Flw rd, imm(.symbol + rs1)) => {
            let rs1 = rs1.unwrap_or(REG_X0);
            let symbol = st.get_zrel(&symbol);
            let imm = symbol + imm as u32;
            assert!(within(imm, 10));
            instr!(Flw[d] rd, imm(rs1))
        }
        pseudo_i!(Sw rs, imm(.symbol + rs1)) => {
            let rs1 = rs1.unwrap_or(REG_X0);
            let symbol = st.get_zrel(&symbol);
            let imm = symbol + imm as u32;
            assert!(within(imm, 10));
            instr!(Sw[d] rs, imm(rs1))
        }
        pseudo_f!(Fsw rs, imm(.symbol + rs1)) => {
            let rs1 = rs1.unwrap_or(REG_X0);
            let symbol = st.get_zrel(&symbol);
            let imm = symbol + imm as u32;
            assert!(within(imm, 10));
            instr!(Fsw[d] rs, imm(rs1))
        }
        pseudo!(Nop) => instr!(I: Addi 0, 0, 0),
        pseudo_i!(Li rd, imm: imm) => {
            let imm = imm as u32;
            let hi = LinkerExpr::hi_u(imm).as_const().unwrap();
            if hi == 0 {
                instr!(I: Addi rd, 0, imm)
            } else {
                unimplemented!("imm {imm} too large")
            }
        }
        pseudo_i!(Mv rd, rs) => instr!(I: Addi rd, rs, 0),
        pseudo_i!(Not rd, rs) => instr!(I: Xori rd, rs, 1),
        #[cfg(not(feature = "isa_2nd"))]
        pseudo_i!(Neg rd, rs) => instr!(R: Sub rd, 0, rs),
        pseudo_f!(Fmv rd, rs) => instr!(F.E: Fsgnj rd, rs, rs),
        pseudo_f!(Fabs rd, rs) => instr!(F.E: Fsgnjx rd, rs, rs),
        pseudo_f!(Fneg rd, rs) => instr!(F.E: Fsgnjn rd, rs, rs),
        #[cfg(not(feature = "isa_2nd"))]
        pseudo_f!(Finv rd, rs) => instr!(F.E: Fdiv rd, 1, rs),
        #[cfg(feature = "isa_2nd")]
        pseudo_f!(Finv rd, rs) => instr!(F.H: Finv rd, rs),
        pseudo_i!(Beqz rs, #offset) => instr!(B: Beq rs, 0, offset),
        pseudo_i!(Bnez rs, #offset) => instr!(B: Bne rs, 0, offset),
        pseudo_i!(Blez rs, #offset) => instr!(B: Bge 0, rs, offset),
        pseudo_i!(Bgez rs, #offset) => instr!(B: Bge rs, 0, offset),
        pseudo_i!(Bltz rs, #offset) => instr!(B: Blt rs, 0, offset),
        pseudo_i!(Bgtz rs, #offset) => instr!(B: Blt 0, rs, offset),
        pseudo_i!(Bgt rs, rt, #offset) => instr!(B: Blt rt, rs, offset),
        pseudo_i!(Ble rs, rt, #offset) => instr!(B: Bge rt, rs, offset),
        #[cfg(feature = "isa_2nd")]
        pseudo_i!(Bgti rs, imm: rt, #offset) => instr!(P: Bgti rs, rt, offset),
        #[cfg(feature = "isa_2nd")]
        pseudo_i!(Blei rs, imm: rt, #offset) => instr!(P: Blei rs, rt, offset),
        pseudo_f!(Fblez rs, #offset) => instr!(F.W: Fbge 0, rs, offset),
        pseudo_f!(Fbgez rs, #offset) => instr!(F.W: Fbge rs, 0, offset),
        pseudo_f!(Fbltz rs, #offset) => instr!(F.W: Fblt rs, 0, offset),
        pseudo_f!(Fbgtz rs, #offset) => instr!(F.W: Fblt 0, rs, offset),
        pseudo_f!(Fbgt rs, rt, #offset) => instr!(F.W: Fblt rt, rs, offset),
        pseudo_f!(Fble rs, rt, #offset) => instr!(F.W: Fbge rt, rs, offset),
        pseudo_i!(J #offset) => instr!(J: Jal 0, offset),
        pseudo_i!(Jal #offset) => instr!(J: Jal 1, offset),
        pseudo_i!(Jr rs) => instr!(I: Jalr 0, rs, 0),
        pseudo_i!(Jalr rs) => instr!(I: Jalr 1, rs, 0),
        pseudo!(Ret) => instr!(I: Jalr 0, 1, 0),
        // base instructions
        pseudo!(End) => instr!(Misc: End),
        pseudo_i!(Add rd, rs1, rs2) => instr!(R: Add rd, rs1, rs2),
        #[cfg(not(feature = "isa_2nd"))]
        pseudo_i!(Sub rd, rs1, rs2) => instr!(R: Sub rd, rs1, rs2),
        pseudo_i!(Xor rd, rs1, rs2) => instr!(R: Xor rd, rs1, rs2),
        #[cfg(not(feature = "isa_2nd"))]
        pseudo_i!(Or  rd, rs1, rs2) => instr!(R: Or  rd, rs1, rs2),
        #[cfg(not(feature = "isa_2nd"))]
        pseudo_i!(And rd, rs1, rs2) => instr!(R: And rd, rs1, rs2),
        #[cfg(not(feature = "isa_2nd"))]
        pseudo_i!(Sll rd, rs1, rs2) => instr!(R: Sll rd, rs1, rs2),
        #[cfg(not(feature = "isa_2nd"))]
        pseudo_i!(Sra rd, rs1, rs2) => instr!(R: Sra rd, rs1, rs2),
        #[cfg(not(feature = "isa_2nd"))]
        pseudo_i!(Slt rd, rs1, rs2) => instr!(R: Slt rd, rs1, rs2),
        #[cfg(feature = "isa_2nd")]
        pseudo_i!(Min rd, rs1, rs2) => instr!(R: Min rd, rs1, rs2),
        #[cfg(feature = "isa_2nd")]
        pseudo_i!(Max rd, rs1, rs2) => instr!(R: Max rd, rs1, rs2),
        pseudo_i!(Addi rd, rs, imm: imm) => instr!(I: Addi rd, rs, imm),
        pseudo_i!(Subi rd, rs, imm: imm) => instr!(I: Addi rd, rs, -imm),
        pseudo_i!(Xori rd, rs, imm: imm) => instr!(I: Xori rd, rs, imm),
        #[cfg(not(feature = "isa_2nd"))]
        pseudo_i!(Ori rd, rs, imm: imm) => instr!(I: Ori rd, rs, imm),
        #[cfg(not(feature = "isa_2nd"))]
        pseudo_i!(Andi rd, rs, imm: imm) => instr!(I: Andi rd, rs, imm),
        pseudo_i!(Slli rd, rs, imm: imm) => instr!(I: Slli rd, rs, imm),
        #[cfg(not(feature = "isa_2nd"))]
        pseudo_i!(Srai rd, rs, imm: imm) => instr!(I: Srai rd, rs, imm),
        #[cfg(not(feature = "isa_2nd"))]
        pseudo_i!(Slti rd, rs, imm: imm) => instr!(I: Slti rd, rs, imm),
        pseudo_i!(Sw[any] rs2, imm(rs1)) => instr!(Sw[any] rs2, imm(rs1)),
        pseudo_i!(Lw[any] rd, imm(rs)) => instr!(Lw[any] rd, imm(rs)),
        pseudo_i!(Beq rs1, rs2, #offset) => instr!(B: Beq rs1, rs2, offset),
        pseudo_i!(Bne rs1, rs2, #offset) => instr!(B: Bne rs1, rs2, offset),
        pseudo_i!(Bge rs1, rs2, #offset) => instr!(B: Bge rs1, rs2, offset),
        pseudo_i!(Blt rs1, rs2, #offset) => instr!(B: Blt rs1, rs2, offset),
        #[cfg(feature = "isa_2nd")]
        pseudo_i!(Bxor rs1, rs2, #offset) => instr!(B: Bxor rs1, rs2, offset),
        #[cfg(feature = "isa_2nd")]
        pseudo_i!(Bxnor rs1, rs2, #offset) => instr!(B: Bxnor rs1, rs2, offset),
        #[cfg(feature = "isa_2nd")]
        pseudo_i!(Beqi rs1, imm: imm2, #offset) => instr!(P: Beqi rs1, imm2, offset),
        #[cfg(feature = "isa_2nd")]
        pseudo_i!(Bnei rs1, imm: imm2, #offset) => instr!(P: Bnei rs1, imm2, offset),
        #[cfg(feature = "isa_2nd")]
        pseudo_i!(Bgei rs1, imm: imm2, #offset) => instr!(P: Bgei rs1, imm2, offset),
        #[cfg(feature = "isa_2nd")]
        pseudo_i!(Blti rs1, imm: imm2, #offset) => instr!(P: Blti rs1, imm2, offset),
        pseudo_f!(Fsw[any] rs2, imm(rs1)) => instr!(Fsw[any] rs2, imm(rs1)),
        pseudo_f!(Flw[any] rd, imm(rs)) => instr!(Flw[any] rd, imm(rs)),
        pseudo_f!(Fbeqz rs, #offset) => instr!(F.V: Fbeqz rs, offset),
        pseudo_f!(Fbnez rs, #offset) => instr!(F.V: Fbnez rs, offset),
        pseudo_i!(Outb rs) => instr!(IO: Outb rs),
        pseudo_i!(Inw rd) => instr!(IO: Inw rd),
        pseudo_f!(Finw rd) => instr!(IO: Finw rd),
        pseudo_f!(Fsqrt rd, rs) => instr!(F.H: Fsqrt rd, rs),
        pseudo_f!(Ffloor rd, rs) => instr!(F.H: Ffloor rd, rs),
        pseudo_f!(Fhalf rd, rs) => instr!(F.H: Fhalf rd, rs),
        pseudo_f!(Fadd rd, rs1, rs2) => instr!(F.E: Fadd rd, rs1, rs2),
        pseudo_f!(Fsub rd, rs1, rs2) => instr!(F.E: Fsub rd, rs1, rs2),
        pseudo_f!(Fmul rd, rs1, rs2) => instr!(F.E: Fmul rd, rs1, rs2),
        pseudo_f!(Fdiv rd, rs1, rs2) => instr!(F.E: Fdiv rd, rs1, rs2),
        pseudo_f!(Fsgnj rd, rs1, rs2) => instr!(F.E: Fsgnj rd, rs1, rs2),
        pseudo_f!(Fsgnjx rd, rs1, rs2) => instr!(F.E: Fsgnjx rd, rs1, rs2),
        pseudo_f!(Fsgnjn rd, rs1, rs2) => instr!(F.E: Fsgnjn rd, rs1, rs2),
        #[cfg(feature = "isa_2nd")]
        pseudo_f!(Fmadd rd, rs1, rs2, rs3) => instr!(F.G: Fmadd rd, rs1, rs2, rs3),
        #[cfg(feature = "isa_2nd")]
        pseudo_f!(Fmsub rd, rs1, rs2, rs3) => instr!(F.G: Fmsub rd, rs1, rs2, rs3),
        #[cfg(feature = "isa_2nd")]
        pseudo_f!(Fnmadd rd, rs1, rs2, rs3) => instr!(F.G: Fnmadd rd, rs1, rs2, rs3),
        #[cfg(feature = "isa_2nd")]
        pseudo_f!(Fnmsub rd, rs1, rs2, rs3) => instr!(F.G: Fnmsub rd, rs1, rs2, rs3),
        pseudo_f!(Fblt rs1, rs2, #offset) => instr!(F.W: Fblt rs1, rs2, offset),
        pseudo_f!(Fbge rs1, rs2, #offset) => instr!(F.W: Fbge rs1, rs2, offset),
        pseudo_misc!(Fitof f[rd], x[rs]) => instr!(F.X: Fitof rd, rs),
        pseudo_misc!(Fftoi x[rd], f[rs]) => instr!(F.Y: Fftoi rd, rs),
        pseudo_misc!(Fiszero x[rd], f[rs]) => instr!(F.Y: Fiszero rd, rs),
        pseudo_misc!(Fispos x[rd], f[rs]) => instr!(F.Y: Fispos rd, rs),
        pseudo_misc!(Fisneg x[rd], f[rs]) => instr!(F.Y: Fisneg rd, rs),
        pseudo_misc!(Flt x[rd], f[rs1], f[rs2]) => instr!(F.K: Flt rd, rs1, rs2),
    };
    smallvec![instr]
}
