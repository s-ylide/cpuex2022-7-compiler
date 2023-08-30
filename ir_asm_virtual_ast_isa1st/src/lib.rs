use ast::{BBinOpKind, ConstKind, FBinOpKind, FTerOpKind, FUnOpKind, IBinOpKind, IUnOpKind};
use ir_asm_ast_isa1st::{
    abi::{self, FRegId, RegId, REG_F0, REG_F1, REG_X0},
    FloatConstMap, GlobalVar, GlobalVarArray, GlobalVarMap, GlobalVarValue,
};
use ordered_float::NotNan;
use pervasives::V_ASM_PERVASIVES;
use smallvec::SmallVec;
use std::{
    borrow::Cow,
    collections::VecDeque,
    fmt::{self, Display},
    ops,
};
use ty::ConcTy;
use typedefs::{Ident, IdentSymbol, IfBinFKind, IfBinIKind, IfUnFKind, IfUnIKind, Label, VarDef};
use util::indented::Indented;

#[derive(Debug, Clone, Hash)]
pub enum SymbOrImm<IReg> {
    Sym(IReg),
    Imm(i32),
}

impl<IReg> SymbOrImm<IReg> {
    pub fn as_ident(&self) -> Option<&IReg> {
        if let Self::Sym(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_mut_ident(&mut self) -> Option<&mut IReg> {
        if let Self::Sym(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl<IReg: fmt::Display> fmt::Display for SymbOrImm<IReg> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymbOrImm::Sym(i) => write!(f, "{i}"),
            SymbOrImm::Imm(i) => write!(f, "{i}"),
        }
    }
}

pub trait IntoInner {
    type Ident;
    fn inner_ref(&self) -> &Self::Ident;
}

pub trait IdSymb {
    fn id(&self) -> &IdentSymbol;
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct IVReg<'a>(pub Ident<'a>);

impl<'a> ops::DerefMut for IVReg<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a> ops::Deref for IVReg<'a> {
    type Target = Ident<'a>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct FVReg<'a>(pub Ident<'a>);

impl<'a> ops::DerefMut for FVReg<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a> ops::Deref for FVReg<'a> {
    type Target = Ident<'a>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Display for IVReg<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)
    }
}

impl Display for FVReg<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", self.0)
    }
}

impl IdSymb for IVReg<'_> {
    fn id(&self) -> &IdentSymbol {
        self.inner_ref().id()
    }
}

impl<'a> IntoInner for IVReg<'a> {
    type Ident = Ident<'a>;

    fn inner_ref(&self) -> &Self::Ident {
        &self.0
    }
}

impl IdSymb for FVReg<'_> {
    fn id(&self) -> &IdentSymbol {
        self.inner_ref().id()
    }
}

impl<'a> IntoInner for FVReg<'a> {
    type Ident = Ident<'a>;

    fn inner_ref(&self) -> &Self::Ident {
        &self.0
    }
}

pub type StmtList<Label, IReg, FReg> = VecDeque<Stmt<Label, IReg, FReg>>;

#[derive(Debug, Clone)]
pub struct BasicBlock<Label, IReg, FReg> {
    pub id: Label,
    pub instrs: StmtList<Label, IReg, FReg>,
    pub terminator: Terminator<IReg, FReg, Label>,
    pub block_param: BlockParamDef<IReg, FReg>,
}

impl<'a, IReg, FReg> BasicBlock<Label<'a>, IReg, FReg> {
    pub fn just_jumps(to: Label<'a>) -> Self {
        Self {
            id: Label::name("runway"),
            instrs: Default::default(),
            terminator: Terminator::Branch(Branch(to, Default::default())),
            block_param: Default::default(),
        }
    }
    pub fn only_terminator(id: Label<'a>, terminator: Terminator<IReg, FReg, Label<'a>>) -> Self {
        Self {
            id,
            instrs: Default::default(),
            terminator,
            block_param: Default::default(),
        }
    }
}

impl<Label, IReg, FReg> BasicBlock<Label, IReg, FReg> {
    pub fn exit_program(&mut self) {
        if let Terminator::Exit = self.terminator {
            self.terminator = Terminator::End;
        }
    }

    pub fn len(&self) -> usize {
        self.instrs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.instrs.is_empty()
    }
}

#[derive(Debug, Clone)]
pub enum Terminator<IReg, FReg, Label> {
    /// End of program
    End,
    /// Exit function (`return;`)
    Exit,
    /// Return from function
    Ret(IorF<IReg, FReg>),
    Branch(Branch<IReg, FReg, Label>),
    CondBr(CondBr<IReg, FReg, Label>),
    TailCall(Label, Vec<IReg>, Vec<FReg>),
}

#[derive(Debug, Clone)]
pub struct Branch<IReg, FReg, Label>(pub Label, pub Vec<BlockParamAssign<IReg, FReg>>);

#[derive(Debug, Clone)]
pub struct CondBr<IReg, FReg, Label>(pub CondBrKind<IReg, FReg>, pub Label, pub Label);

impl<IReg, FReg, Label> Terminator<IReg, FReg, Label> {
    #[inline]
    pub fn dests(&self) -> impl Iterator<Item = &Label> {
        use Terminator::*;
        let mut v = Vec::new();
        match self {
            Ret(_) | Exit | End | TailCall(..) => (),
            Branch(self::Branch(l, _)) => {
                v.push(l);
            }
            CondBr(self::CondBr(_, l1, l2)) => {
                v.push(l1);
                v.push(l2);
            }
        }
        v.into_iter()
    }
    #[inline]
    pub fn is_exit(&self) -> bool {
        self.out_degree() == 0
    }
    #[inline]
    pub fn out_degree(&self) -> usize {
        use Terminator::*;
        match self {
            Ret(..) | Exit | End | TailCall(..) => 0,
            Branch(..) => 1,
            CondBr(..) => 2,
        }
    }
    pub fn as_simple_br(&self) -> Option<&Label> {
        if let Self::Branch(Branch(v, assigns)) = self {
            assigns.is_empty().then_some(v)
        } else {
            None
        }
    }
    pub fn as_condbr_then_mut(&mut self) -> Option<&mut Label> {
        if let Self::CondBr(CondBr(_, v, _)) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_condbr_else_mut(&mut self) -> Option<&mut Label> {
        if let Self::CondBr(CondBr(_, _, v)) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_condbr_flip(&mut self) {
        if let Self::CondBr(CondBr(cc, l1, l2)) = self {
            std::mem::swap(l1, l2);
            cc.filp_cond();
        }
    }

    pub fn as_paramed_br(&self) -> Option<BrWithParamRef<'_, IReg, FReg, Label>> {
        if let Terminator::Branch(Branch(l, p)) = self {
            Some(BrWithParamRef(l, p))
        } else {
            None
        }
    }

    pub fn as_mut_paramed_br(&mut self) -> Option<BrWithParamRefMut<'_, IReg, FReg, Label>> {
        if let Terminator::Branch(Branch(l, p)) = self {
            Some(BrWithParamRefMut(l, p))
        } else {
            None
        }
    }

    pub fn as_mut_br(&mut self) -> BrDest<BrWithOptParamRefMut<'_, IReg, FReg, Label>> {
        if let Terminator::CondBr(CondBr(_, l1, l2)) = self {
            BrDest::Double(
                BrWithOptParamRefMut(l1, None),
                BrWithOptParamRefMut(l2, None),
            )
        } else if let Terminator::Branch(Branch(l, p)) = self {
            BrDest::Single(BrWithOptParamRefMut(l, Some(p)))
        } else {
            BrDest::None
        }
    }

    pub fn as_mut_condbr(&mut self) -> Option<&mut CondBr<IReg, FReg, Label>> {
        if let Self::CondBr(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

pub struct BrWithParamRef<'a, IReg, FReg, Label>(
    pub &'a Label,
    pub &'a Vec<BlockParamAssign<IReg, FReg>>,
);

pub struct BrWithParamRefMut<'a, IReg, FReg, Label>(
    pub &'a mut Label,
    pub &'a mut Vec<BlockParamAssign<IReg, FReg>>,
);

pub struct BrWithOptParamRefMut<'a, IReg, FReg, Label>(
    pub &'a mut Label,
    pub Option<&'a mut Vec<BlockParamAssign<IReg, FReg>>>,
);

pub enum BrDest<T> {
    None,
    Single(T),
    Double(T, T),
}

impl<T> IntoIterator for BrDest<T> {
    type Item = T;

    type IntoIter = <SmallVec<[T; 2]> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            BrDest::None => smallvec::smallvec![].into_iter(),
            BrDest::Single(v) => smallvec::smallvec![v].into_iter(),
            BrDest::Double(v1, v2) => smallvec::smallvec![v1, v2].into_iter(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum CondBrKind<I, F> {
    /// cond, lhs, rhs, then (bb label), else (bb label); `if cond($lhs, $rhs) { $then } else { $else }`
    IfBin(IfBinIKind, I, SymbOrImm<I>),
    IfBinF(IfBinFKind, FReg<F>, FReg<F>),
    /// cond, lhs, then (bb label), else (bb label); `if cond($lhs, 0) { $then } else { $else }`
    IfUn(IfUnIKind, I),
    IfUnF(IfUnFKind, FReg<F>),
}

impl<IReg, FReg> CondBrKind<IReg, FReg> {
    pub fn filp_cond(&mut self) {
        match self {
            CondBrKind::IfBin(k, _, _) => *k = k.negated(),
            CondBrKind::IfBinF(k, _, _) => *k = k.negated(),
            CondBrKind::IfUn(k, _) => *k = k.negated(),
            CondBrKind::IfUnF(k, _) => *k = k.negated(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct BlockParamAssign<IReg, FReg> {
    /// this parameter constructed later
    rhs: Option<IorF<IReg, FReg>>,
    pub param: LetBound<IReg, FReg>,
}

impl<IReg: fmt::Display, FReg: fmt::Display> fmt::Display for BlockParamAssign<IReg, FReg> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let rhs = self.rhs();
        write!(f, "{} := {rhs}", self.param)
    }
}

impl<IReg, FReg> BlockParamAssign<IReg, FReg> {
    pub fn from_assign(param: LetBound<IReg, FReg>, rhs: IorF<IReg, FReg>) -> Self {
        Self {
            rhs: Some(rhs),
            param,
        }
    }
    pub fn new(param: LetBound<IReg, FReg>) -> Self {
        Self { rhs: None, param }
    }
    pub fn rhs(&self) -> &IorF<IReg, FReg> {
        self.rhs.as_ref().unwrap()
    }
    pub fn set_rhs(&mut self, v: IorF<IReg, FReg>) {
        self.rhs = Some(v);
    }
    pub fn into_inner(self) -> (IorF<IReg, FReg>, LetBound<IReg, FReg>) {
        (self.rhs.unwrap(), self.param)
    }

    pub fn rhs_mut(&mut self) -> &mut IorF<IReg, FReg> {
        self.rhs.as_mut().unwrap()
    }
}

#[derive(Debug, Clone)]
pub struct LetBound<I, F> {
    pub name: IorF<I, F>,
    pub ty: Option<ConcTy>,
}

impl<IReg: fmt::Display, FReg: fmt::Display> fmt::Display for LetBound<IReg, FReg> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let LetBound { name, ty } = &self;
        match ty {
            Some(ty) => write!(f, "{name}: {ty}"),
            None => write!(f, "{name}"),
        }
    }
}

pub type LetBoundKind<I, F> = Option<LetBound<I, F>>;

pub type BlockParamDef<I, F> = Vec<LetBound<I, F>>;

impl<'a> LetBound<IVReg<'a>, FVReg<'a>> {
    pub fn from_vardef(value: VarDef<'a>) -> Option<Self> {
        let c = value.ty.as_concty().unwrap();
        IorF::from_vardef(Cow::Owned(value)).map(|name| Self { name, ty: Some(c) })
    }
}

#[derive(Debug, Clone)]
pub enum Stmt<Label, I, F> {
    /// ad-hoc ABI-dependent statement; `addi rd, rs, imm`
    IncrABI(RegId, i32),
    Assign(Option<IorF<I, F>>, Option<ConcTy>, Expr<Label, I, F>),
    /// rs2, rs1, displacement; `M[rs1 + displacement] <- rs2`
    Store(IReg<I>, IReg<I>, i32),
    StoreF(FReg<F>, IReg<I>, i32),
    StoreLabelDisp(IReg<I>, Option<IReg<I>>, Label, i32),
    StoreFLabelDisp(FReg<F>, Option<IReg<I>>, Label, i32),
}

impl<Label: Display, I: Display, F: Display> Display for Stmt<Label, I, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Stmt::IncrABI(r, imm) => write!(f, "addi {r}, {r}, {imm}"),
            Stmt::Assign(None, _, e) => write!(f, "{e}"),
            Stmt::Assign(Some(v), Some(ty), e) => write!(f, "let {v} : {ty} = {e}"),
            Stmt::Assign(Some(v), None, e) => write!(f, "let {v} = {e}"),
            Stmt::Store(r2, r1, imm) => write!(f, "{imm}({r1}) <- {r2}"),
            Stmt::StoreF(r2, r1, imm) => write!(f, "{imm}({r1}) <- {r2}"),
            Stmt::StoreLabelDisp(r2, None, l, imm) => write!(f, "{imm}(^{l}) <- {r2}"),
            Stmt::StoreFLabelDisp(r2, None, l, imm) => write!(f, "{imm}(^{l}) <- {r2}"),
            Stmt::StoreLabelDisp(r2, Some(r1), l, imm) => write!(f, "{imm}(^{l} + {r1}) <- {r2}"),
            Stmt::StoreFLabelDisp(r2, Some(r1), l, imm) => write!(f, "{imm}(^{l} + {r1}) <- {r2}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IorF<I, F> {
    I(I),
    F(F),
}

impl<'a> IorF<IVReg<'a>, FVReg<'a>> {
    pub fn from_vardef(vd: Cow<VarDef<'a>>) -> Option<Self> {
        Self::from_name_ty(Cow::Borrowed(&vd.name), &vd.ty.as_concty().unwrap())
    }
    pub fn from_name_ty(name: Cow<Ident<'a>>, cty: &ConcTy) -> Option<Self> {
        abi::RegKind::from_concty(cty).map(|c| match c {
            abi::RegKind::Int => Self::I(IVReg(name.into_owned())),
            abi::RegKind::Float => Self::F(FVReg(name.into_owned())),
        })
    }
}

impl<T, I: ops::DerefMut<Target = T>, F: ops::DerefMut<Target = T>> ops::DerefMut for IorF<I, F> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            IorF::I(t) => &mut **t,
            IorF::F(t) => &mut **t,
        }
    }
}

impl<T, I: ops::Deref<Target = T>, F: ops::Deref<Target = T>> ops::Deref for IorF<I, F> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            IorF::I(t) => &**t,
            IorF::F(t) => &**t,
        }
    }
}

impl<I, F> IorF<I, F> {
    pub fn ty(&self) -> abi::RegKind {
        match self {
            IorF::I(..) => abi::RegKind::Int,
            IorF::F(..) => abi::RegKind::Float,
        }
    }

    pub fn as_i(&self) -> Option<&I> {
        if let Self::I(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_f(&self) -> Option<&F> {
        if let Self::F(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl<'a> IntoInner for IorF<IVReg<'a>, FVReg<'a>> {
    type Ident = Ident<'a>;

    fn inner_ref(&self) -> &Self::Ident {
        match self {
            IorF::I(i) => i.inner_ref(),
            IorF::F(f) => f.inner_ref(),
        }
    }
}

impl<I: Display, F: Display> Display for IorF<I, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IorF::I(i) => write!(f, "{i}"),
            IorF::F(ff) => write!(f, "{ff}"),
        }
    }
}

pub mod builder {

    use std::borrow::Cow;

    use super::*;

    pub fn assign<'a, L>(
        name: Cow<Ident<'a>>,
        cty: ConcTy,
        e: Expr<L, IVReg<'a>, FVReg<'a>>,
    ) -> Stmt<L, IVReg<'a>, FVReg<'a>> {
        Stmt::Assign(IorF::from_name_ty(name, &cty), Some(cty), e)
    }

    pub fn discard<'a, L>(e: Expr<L, IVReg<'a>, FVReg<'a>>) -> Stmt<L, IVReg<'a>, FVReg<'a>> {
        Stmt::Assign(None, None, e)
    }

    pub fn cp_from<'a, L>(iorf: IorF<IVReg<'a>, FVReg<'a>>) -> Expr<L, IVReg<'a>, FVReg<'a>> {
        match iorf {
            IorF::I(i) => Expr::Mov(PhysOrVirt::V(i)),
            IorF::F(f) => Expr::MovF(PhysOrVirt::V(f)),
        }
    }
}

pub type IReg<I> = PhysOrVirt<RegId, I>;
pub type FReg<F> = PhysOrVirt<FRegId, F>;

#[derive(Debug, Clone)]
/// physical or virtual register
pub enum PhysOrVirt<P, V> {
    P(P),
    V(V),
}

impl<P: Display, V: Display> Display for PhysOrVirt<P, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PhysOrVirt::P(p) => write!(f, "{p}"),
            PhysOrVirt::V(v) => write!(f, "{v}"),
        }
    }
}

impl<P, V> PhysOrVirt<P, V> {
    pub fn as_p(&self) -> Option<&P> {
        if let Self::P(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_v(&self) -> Option<&V> {
        if let Self::V(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_mut_v(&mut self) -> Option<&mut V> {
        if let Self::V(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl<R> PhysOrVirt<R, R> {
    pub fn inner(self) -> R {
        match self {
            PhysOrVirt::P(r) => r,
            PhysOrVirt::V(r) => r,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr<Label, I, F> {
    Nop,
    LoadInt(i32),
    LoadF32(NotNan<f32>),
    LoadLabelAddr(Label),
    Mov(IReg<I>),
    MovF(FReg<F>),
    IUnOp(IUnOpKind, I),
    BBinOp(BBinOpKind, I, I),
    IBinOp(IBinOpKind, I, SymbOrImm<I>),
    FUnOp(FUnOpKind, FReg<F>),
    FBinOp(FBinOpKind, FReg<F>, FReg<F>),
    FTerOp(FTerOpKind, FReg<F>, FReg<F>, FReg<F>),
    /// base, displacement; base + displacement : to be loaded pointer
    Load(IReg<I>, i32),
    LoadFromLabelDisp(Option<IReg<I>>, Label, i32),
    /// function address (Label), integer args, float args
    CallDirectly(Label, Vec<I>, Vec<F>),
    Intrinsic(String, Vec<I>, Vec<F>),
}

impl<Label, I, F> Expr<Label, I, F> {
    pub fn has_effect(&self) -> bool {
        match self {
            Expr::CallDirectly(..) => true,
            Expr::Intrinsic(f, ..) => V_ASM_PERVASIVES.get(f.as_str()).unwrap().has_effect,
            _ => false,
        }
    }
    pub fn const_eval(&self) -> Option<ConstKind> {
        use PhysOrVirt::*;
        match self {
            Expr::LoadInt(i) => Some(ConstKind::Int(*i)),
            Expr::Mov(P(REG_X0)) => Some(ConstKind::Int(0)),
            Expr::MovF(P(REG_F0)) => Some(ConstKind::Float(NotNan::new(0.0).unwrap())),
            Expr::MovF(P(REG_F1)) => Some(ConstKind::Float(NotNan::new(1.0).unwrap())),
            _ => None,
        }
    }
}

impl<Label: Display, IReg: Display, FReg: Display> Display for Expr<Label, IReg, FReg> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Nop => write!(f, "nop"),
            Expr::LoadInt(i) => write!(f, "${i}"),
            Expr::LoadF32(l) => write!(f, "${l}"),
            Expr::LoadLabelAddr(l) => write!(f, "mv #^{l}"),
            Expr::Mov(r) => write!(f, "{r} as i32"),
            Expr::MovF(r) => write!(f, "{r} as f32"),
            Expr::IUnOp(kind, r) => match kind {
                IUnOpKind::Not => write!(f, "!{r} as i32"),
                IUnOpKind::Neg => write!(f, "-{r} as i32"),
                IUnOpKind::ItoF => write!(f, "{r} as f32"),
            },
            Expr::FUnOp(kind, r) => match kind {
                FUnOpKind::Fneg => write!(f, "-{r} as f32"),
                FUnOpKind::Sqrt => write!(f, "sqrt({r}) as f32"),
                FUnOpKind::Floor => write!(f, "floor({r}) as f32"),
                FUnOpKind::Finv => write!(f, "finv({r}) as f32"),
                FUnOpKind::Ftoi => write!(f, "{r} as i32"),
                FUnOpKind::Fiszero => write!(f, "{r} == 0.0 as i32"),
                FUnOpKind::Fispos => write!(f, "{r} > 0.0 as i32"),
                FUnOpKind::Fisneg => write!(f, "{r} < 0.0 as i32"),
            },
            Expr::BBinOp(kind, a, b) => {
                let symb = kind.symbol();
                write!(f, "{a} {symb} {b}")
            }
            Expr::IBinOp(kind, a, b) => {
                let symb = kind.symbol();
                write!(f, "{a} {symb} ")?;
                match b {
                    SymbOrImm::Sym(b) => write!(f, "{b}"),
                    SymbOrImm::Imm(imm) => write!(f, "${imm}"),
                }
            }
            Expr::FBinOp(kind, a, b) => {
                let symb = match kind {
                    FBinOpKind::FAdd => "+.",
                    FBinOpKind::FSub => "-.",
                    FBinOpKind::FMul => "*.",
                    FBinOpKind::FDiv => "/.",
                    FBinOpKind::Fless => "<",
                };
                write!(f, "{a} {symb} {b}")
            }
            Expr::FTerOp(kind, a, b, c) => match kind {
                FTerOpKind::Fmadd => write!(f, "{a} *. {b} +. {c}"),
                FTerOpKind::Fmsub => write!(f, "{a} *. {b} -. {c}"),
                FTerOpKind::Fnmadd => write!(f, "-{a} *. {b} +. {c}"),
                FTerOpKind::Fnmsub => write!(f, "-{a} *. {b} -. {c}"),
            },
            Expr::Load(r, i) => write!(f, "{i}({r})"),
            Expr::LoadFromLabelDisp(None, l, i) => write!(f, "{i}(^{l})"),
            Expr::LoadFromLabelDisp(Some(r), l, i) => write!(f, "{i}(^{l} + {r})"),
            Expr::CallDirectly(l, args, fargs) => write!(
                f,
                "call {l} i:({}) f:({})",
                args.iter()
                    .map(|a| format!("{a}"))
                    .collect::<Vec<String>>()
                    .join(", "),
                fargs
                    .iter()
                    .map(|a| format!("{a}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Expr::Intrinsic(l, args, fargs) => write!(
                f,
                "{l} i:({}) f:({})",
                args.iter()
                    .map(|a| format!("{a}"))
                    .collect::<Vec<String>>()
                    .join(", "),
                fargs
                    .iter()
                    .map(|a| format!("{a}"))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunDef<Label, IReg, FReg> {
    pub name: Label,
    pub args: Vec<(IReg, ConcTy)>,
    pub fargs: Vec<(FReg, ConcTy)>,
    pub body: VecDeque<BasicBlock<Label, IReg, FReg>>,
    pub ret: ConcTy,
}

impl<Label: Display, IReg: Display, FReg: Display> Display for FunDef<Label, IReg, FReg> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn {}", self.name)?;
        write!(
            f,
            " i:({})",
            self.args
                .iter()
                .map(|(a, t)| format!("{a}: {t}"))
                .collect::<Vec<String>>()
                .join(", ")
        )?;
        write!(
            f,
            " f:({})",
            self.fargs
                .iter()
                .map(|(a, t)| format!("{a}: {t}"))
                .collect::<Vec<String>>()
                .join(", ")
        )?;
        writeln!(f, " -> {} {{", self.ret)?;
        for BasicBlock {
            id,
            instrs,
            terminator,
            block_param,
        } in self.body.iter()
        {
            write!(f, "^{id}")?;
            if !block_param.is_empty() {
                write!(
                    f,
                    " ({})",
                    block_param
                        .iter()
                        .map(|a| format!("{a}"))
                        .collect::<Vec<String>>()
                        .join(", ")
                )?;
            }
            writeln!(f, ":")?;
            for instr in instrs {
                writeln!(f, "\t{instr}")?;
            }
            write!(f, "\t")?;
            match terminator {
                Terminator::End => writeln!(f, "end")?,
                Terminator::Exit => writeln!(f, "ret")?,
                Terminator::Ret(r) => writeln!(f, "ret {r}")?,
                Terminator::Branch(Branch(l, lbs)) if !lbs.is_empty() => writeln!(
                    f,
                    "br ^{l} ({})",
                    lbs.iter()
                        .map(|a| format!("{a}"))
                        .collect::<Vec<String>>()
                        .join(", "),
                )?,
                Terminator::Branch(Branch(l, _)) => writeln!(f, "br ^{l}")?,
                Terminator::CondBr(CondBr(c, l1, l2)) => match c {
                    CondBrKind::IfBin(kind, r1, r2) => {
                        let op = kind.symbol();
                        writeln!(f, "if {r1} {op} {r2} then br ^{l1} else br ^{l2}")?;
                    }
                    CondBrKind::IfBinF(kind, r1, r2) => {
                        let op = kind.symbol();
                        writeln!(f, "if {r1} {op} {r2} then br ^{l1} else br ^{l2}")?;
                    }
                    CondBrKind::IfUn(kind, r1) => {
                        let op = kind.symbol();
                        writeln!(f, "if {r1} {op} 0 then br ^{l1} else br ^{l2}")?;
                    }
                    CondBrKind::IfUnF(kind, r1) => {
                        let op = kind.symbol();
                        writeln!(f, "if {r1} {op} 0.0 then br ^{l1} else br ^{l2}")?;
                    }
                },
                Terminator::TailCall(l, args, fargs) => writeln!(
                    f,
                    "tail {l} i:({}) f:({})",
                    args.iter()
                        .map(|a| format!("{a}"))
                        .collect::<Vec<String>>()
                        .join(", "),
                    fargs
                        .iter()
                        .map(|a| format!("{a}"))
                        .collect::<Vec<String>>()
                        .join(", ")
                )?,
            }
        }
        writeln!(f, "}}")
    }
}

#[derive(Debug, Clone)]
pub struct Prog<Ident, Label, FunDef> {
    pub float_map: FloatConstMap<Label>,
    pub globals_map: GlobalVarMap<Ident>,
    pub fundefs: Vec<FunDef>,
    pub entry_point: Label,
}

impl<Ident: Display, Label: Display, FunDef: Display> Display for Prog<Ident, Label, FunDef> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.float_map.is_empty() || !self.globals_map.is_empty() {
            use std::fmt::Write;
            let mut f = Indented::new(f, "  ");
            f.indent(1);
            write!(f, "const DATA = {{")?;
            for GlobalVar {
                name, size, value, ..
            } in self.globals_map.data.iter()
            {
                writeln!(f)?;
                write!(f, "{name}: {size} => ")?;
                match value {
                    GlobalVarValue::Array(a) => {
                        let GlobalVarArray {
                            count,
                            data,
                            modification,
                        } = a;
                        write!(f, "[{data}; {count}]")?;
                        if !modification.is_empty() {
                            f.indent(1);
                            for (i, v) in modification {
                                writeln!(f)?;
                                write!(f, ".({i}) = {v}")?;
                            }
                            f.dedent(1);
                        }
                        write!(f, ",")?;
                    }
                    GlobalVarValue::EmptyArray => todo!("this will have been folded into 0"),
                    GlobalVarValue::Tuple(t) => {
                        write!(
                            f,
                            "({})",
                            t.iter()
                                .map(|c| format!("{c}"))
                                .collect::<Vec<_>>()
                                .join(", ")
                        )?;
                    }
                    GlobalVarValue::Const(c) => write!(f, "{c},")?,
                }
            }
            let mut v: Vec<_> = self.float_map.iter().collect();
            v.sort_by_key(|a| a.0);
            for (repr, (label, _)) in v {
                writeln!(f)?;
                write!(f, "{label} => 0x{repr:08X},")?;
            }
            f.dedent(1);
            writeln!(f)?;
            writeln!(f, "}}")?;
            writeln!(f)?;
        }
        writeln!(f, "entrypoint {}", self.entry_point)?;
        for func in &self.fundefs {
            writeln!(f)?;
            write!(f, "{func}")?;
        }
        Ok(())
    }
}

pub type VAsmFunDef<'a> = FunDef<Label<'a>, IVReg<'a>, FVReg<'a>>;
pub type AsmFunDef<'a> = FunDef<Label<'a>, RegId, FRegId>;
pub type VirtualAsm<'a> = Prog<Ident<'a>, Label<'a>, VAsmFunDef<'a>>;
