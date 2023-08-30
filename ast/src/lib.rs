use std::{
    fmt::Display,
    ops::{Deref, DerefMut},
};

use ordered_float::NotNan;
use span::Loc;
use ty::{CTy, ConcTy, FnTy};

use {span::Spanned, ty::Ty};

#[derive(Debug, Clone, PartialEq)]
pub struct VarDef<'a> {
    pub name: Ident<'a>,
    pub ty: Ty,
}

impl<'a> VarDef<'a> {
    pub fn intro_tyvar(name: Ident<'a>) -> Self {
        Self {
            name,
            ty: Ty::new_typevar(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunDef<'a> {
    pub var: VarDef<'a>,
    pub args: Vec<VarDef<'a>>,
    pub body: Box<Expr<'a>>,
    pub ret_ty: Ty,
}

impl<'a> FunDef<'a> {
    pub fn new(name: Ident<'a>, args: Vec<Ident<'a>>, body: Box<Expr<'a>>) -> Self {
        Self {
            var: VarDef::intro_tyvar(name),
            args: args.into_iter().map(VarDef::intro_tyvar).collect(),
            body,
            ret_ty: Ty::new_typevar(),
        }
    }
    pub fn get_ty(&self) -> FnTy {
        FnTy {
            arg: self
                .args
                .iter()
                .map(|xt| xt.ty.as_concty().unwrap())
                .collect(),
            ret: self.ret_ty.as_concty().unwrap(),
        }
    }
}

pub type Ident<'a> = &'a str;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BBinOpKind {
    Eq,
    Le,
    Ge,
    Ne,
    Lt,
    Gt,
}

impl BBinOpKind {
    pub fn eval(&self, lhs: i32, rhs: i32) -> bool {
        match self {
            BBinOpKind::Eq => lhs == rhs,
            BBinOpKind::Le => lhs <= rhs,
            BBinOpKind::Ge => lhs >= rhs,
            BBinOpKind::Ne => lhs != rhs,
            BBinOpKind::Lt => lhs < rhs,
            BBinOpKind::Gt => lhs > rhs,
        }
    }
    pub fn symbol(&self) -> &'static str {
        match self {
            BBinOpKind::Eq => "==",
            BBinOpKind::Le => "<=",
            BBinOpKind::Ge => ">=",
            BBinOpKind::Ne => "!=",
            BBinOpKind::Lt => "<",
            BBinOpKind::Gt => ">",
        }
    }
    pub fn negated(&self) -> Self {
        match self {
            BBinOpKind::Eq => BBinOpKind::Ne,
            BBinOpKind::Le => BBinOpKind::Gt,
            BBinOpKind::Ge => BBinOpKind::Lt,
            BBinOpKind::Ne => BBinOpKind::Eq,
            BBinOpKind::Lt => BBinOpKind::Ge,
            BBinOpKind::Gt => BBinOpKind::Le,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IBinOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Sll,
    Srl,
    Xor,
    Or,
    Min,
    Max,
}

impl IBinOpKind {
    pub fn eval(&self, lhs: i32, rhs: i32) -> i32 {
        match self {
            IBinOpKind::Add => lhs + rhs,
            IBinOpKind::Sub => lhs - rhs,
            IBinOpKind::Mul => lhs * rhs,
            IBinOpKind::Div => lhs / rhs,
            IBinOpKind::Sll => lhs << rhs,
            IBinOpKind::Srl => lhs >> rhs,
            IBinOpKind::Xor => lhs ^ rhs,
            IBinOpKind::Or => lhs | rhs,
            IBinOpKind::Min => lhs.min(rhs),
            IBinOpKind::Max => lhs.max(rhs),
        }
    }
    pub fn symbol(&self) -> &'static str {
        match self {
            IBinOpKind::Add => "+",
            IBinOpKind::Sub => "-",
            IBinOpKind::Mul => "*",
            IBinOpKind::Div => "/",
            IBinOpKind::Sll => "<<",
            IBinOpKind::Srl => ">>",
            IBinOpKind::Xor => "^",
            IBinOpKind::Or => "|",
            IBinOpKind::Min => "min",
            IBinOpKind::Max => "max",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub enum IUnOpKind {
    Not,
    Neg,
    ItoF,
}

impl IUnOpKind {
    pub fn eval(&self, i: i32) -> ConstKind {
        use ConstKind::*;
        match self {
            IUnOpKind::Not => Int(i ^ 1),
            IUnOpKind::Neg => Int(-i),
            IUnOpKind::ItoF => Float(NotNan::new(i as f32).unwrap()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FTerOpKind {
    Fmadd,
    Fmsub,
    Fnmadd,
    Fnmsub,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FBinOpKind {
    FAdd,
    FSub,
    FMul,
    FDiv,
    Fless,
}

impl FBinOpKind {
    pub fn eval(&self, lhs: f32, rhs: f32) -> ConstKind {
        use ConstKind::*;
        match self {
            FBinOpKind::FAdd => Float(NotNan::new(lhs + rhs).unwrap()),
            FBinOpKind::FSub => Float(NotNan::new(lhs - rhs).unwrap()),
            FBinOpKind::FMul => Float(NotNan::new(lhs * rhs).unwrap()),
            FBinOpKind::FDiv => Float(NotNan::new(lhs / rhs).unwrap()),
            FBinOpKind::Fless => Bool(lhs < rhs),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub enum FUnOpKind {
    Fneg,
    Sqrt,
    Floor,
    Finv,
    Fiszero,
    Fispos,
    Fisneg,
    Ftoi,
}

impl FUnOpKind {
    pub fn eval(&self, f: f32) -> ConstKind {
        use ConstKind::*;
        match self {
            FUnOpKind::Fneg => Float(NotNan::new(-f).unwrap()),
            FUnOpKind::Sqrt => Float(NotNan::new(f.sqrt()).unwrap()),
            FUnOpKind::Floor => Float(NotNan::new(f.floor()).unwrap()),
            FUnOpKind::Finv => Float(NotNan::new(1.0 / f).unwrap()),
            FUnOpKind::Fiszero => Bool(f == 0.0),
            FUnOpKind::Fispos => Bool(f > 0.0),
            FUnOpKind::Fisneg => Bool(f < 0.0),
            FUnOpKind::Ftoi => Int(f as i32),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TerOpKind {
    FTerOp(FTerOpKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOpKind {
    BBinOp(BBinOpKind),
    IBinOp(IBinOpKind),
    FBinOp(FBinOpKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOpKind {
    Not,
    Neg,
    FNeg,
    Fiszero,
    Fispos,
    Fisneg,
}

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq)]
pub enum ConstKind {
    Unit,
    Bool(bool),
    Int(i32),
    Float(NotNan<f32>),
}

impl ConstKind {
    pub fn get_concty(&self) -> ConcTy {
        use ConcTy::*;
        match self {
            ConstKind::Unit => Unit,
            ConstKind::Bool(_) => Bool,
            ConstKind::Int(_) => Int,
            ConstKind::Float(_) => Float,
        }
    }
    pub fn as_zero(&self) -> Option<()> {
        match self {
            ConstKind::Unit => None,
            ConstKind::Bool(b) => (!*b).then_some(()),
            ConstKind::Int(i) => match i {
                0 => Some(()),
                _ => None,
            },
            ConstKind::Float(f) => {
                if *f == 0.0 {
                    Some(())
                } else {
                    None
                }
            }
        }
    }
}

impl Default for ConstKind {
    fn default() -> Self {
        Self::Unit
    }
}

impl Display for ConstKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstKind::Unit => write!(f, "()"),
            ConstKind::Bool(b) => write!(f, "{b}"),
            ConstKind::Int(i) => write!(f, "{i}"),
            ConstKind::Float(fl) => write!(f, "{fl}"),
        }
    }
}

impl ConstKind {
    pub fn as_int(&self) -> Option<&i32> {
        if let Self::Int(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_bool(&self) -> Option<&bool> {
        if let Self::Bool(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_float(&self) -> Option<&f32> {
        if let Self::Float(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum LetKind<'a> {
    LetVar(VarDef<'a>, Box<Expr<'a>>, Box<Expr<'a>>),
    LetRec(FunDef<'a>, Box<Expr<'a>>),
    LetTuple(Vec<VarDef<'a>>, Box<Expr<'a>>, Box<Expr<'a>>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind<'a> {
    Const(ConstKind),
    UnOp(UnOpKind, Box<Expr<'a>>),
    BinOp(BinOpKind, Box<Expr<'a>>, Box<Expr<'a>>),
    TerOp(TerOpKind, Box<Expr<'a>>, Box<Expr<'a>>, Box<Expr<'a>>),
    If(Box<Expr<'a>>, Box<Expr<'a>>, Box<Expr<'a>>),
    Then(Box<Expr<'a>>, Box<Expr<'a>>),
    Var(Typed<Ident<'a>>),
    LibFun(Ident<'a>, FnTy),
    App(Box<Expr<'a>>, Vec<Expr<'a>>),
    Tuple(Vec<Expr<'a>>),
    Let(LetKind<'a>),
    ArrayMake(Box<Expr<'a>>, Box<Expr<'a>>),
    PrintInt(Box<Expr<'a>>),
    Get(Box<Expr<'a>>, Box<Expr<'a>>),
    Set(Box<Expr<'a>>, Box<Expr<'a>>, Box<Expr<'a>>),
}

impl<'a> ExprKind<'a> {
    pub fn discriminant(&self) -> ExprDiscriminant {
        match self {
            ExprKind::Const(..) => ExprDiscriminant::Const,
            ExprKind::UnOp(k, ..) => ExprDiscriminant::UnOp(*k),
            ExprKind::BinOp(k, ..) => ExprDiscriminant::BinOp(*k),
            ExprKind::TerOp(k, ..) => ExprDiscriminant::TerOp(*k),
            ExprKind::If(..) => ExprDiscriminant::If,
            ExprKind::Then(..) => ExprDiscriminant::Then,
            ExprKind::Var(..) => ExprDiscriminant::Var,
            ExprKind::LibFun(..) => ExprDiscriminant::LibFun,
            ExprKind::App(..) => ExprDiscriminant::App,
            ExprKind::Tuple(..) => ExprDiscriminant::Tuple,
            ExprKind::Let(lk) => match lk {
                LetKind::LetVar(..) => ExprDiscriminant::LetVar,
                LetKind::LetRec(..) => ExprDiscriminant::LetRec,
                LetKind::LetTuple(..) => ExprDiscriminant::LetTuple,
            },
            ExprKind::ArrayMake(..) => ExprDiscriminant::ArrayMake,
            ExprKind::PrintInt(..) => ExprDiscriminant::PrintInt,
            ExprKind::Get(..) => ExprDiscriminant::Get,
            ExprKind::Set(..) => ExprDiscriminant::Set,
        }
    }
}

#[derive(Hash, PartialEq, Eq)]
pub enum ExprDiscriminant {
    Const,
    UnOp(UnOpKind),
    BinOp(BinOpKind),
    TerOp(TerOpKind),
    If,
    Then,
    Var,
    LibFun,
    App,
    Tuple,
    LetVar,
    LetRec,
    LetTuple,
    ArrayMake,
    PrintInt,
    Get,
    Set,
}

impl<'a> ExprKind<'a> {
    pub fn as_const(&self) -> Option<&ConstKind> {
        if let Self::Const(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_libfun(&self) -> Option<(&Ident<'a>, &FnTy)> {
        if let Self::LibFun(f, t) = self {
            Some((f, t))
        } else {
            None
        }
    }
}

impl<'a> Default for ExprKind<'a> {
    fn default() -> Self {
        Self::Const(ConstKind::Unit)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Typed<T> {
    pub item: T,
    pub ty: Option<Ty>,
}

impl<T> Typed<T> {
    pub fn new(item: T) -> Self {
        Self { item, ty: None }
    }
}

impl<T> Deref for Typed<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

impl<T> DerefMut for Typed<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.item
    }
}

pub type Expr<'a> = Typed<Spanned<ExprKind<'a>>>;

pub fn typed_expr(item: ExprKind, cty: CTy) -> Expr {
    Typed {
        item: Spanned::somewhere(item),
        ty: Some(Ty::C(cty)),
    }
}

pub fn typed_var(item: Ident, cty: CTy) -> Expr {
    let ty = Ty::C(cty.clone());
    typed_expr(ExprKind::Var(Typed { item, ty: Some(ty) }), cty)
}

pub fn wrap(item: ExprKind, span: (Loc, Loc)) -> Expr {
    Typed {
        item: Spanned::new(item, span),
        ty: None,
    }
}
