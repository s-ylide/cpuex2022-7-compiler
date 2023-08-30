mod inlining;
mod transform;

use ir_knorm::Continue;

pub use inlining::inlining_arg;
pub use transform::closure_transform;

use ast::{BBinOpKind, ConstKind, FBinOpKind, FTerOpKind, FUnOpKind, IBinOpKind, IUnOpKind};
use std::collections::{HashMap, HashSet};
use ty::Ty;
use typedefs::{Ident, IfBranch, IfCond, IfExpr, Label, MaybeConst, VarDef};

#[derive(Debug, Clone)]
pub enum IrNode<'a> {
    Const(ConstKind),
    IUnOp(IUnOpKind, Ident<'a>),
    BBinOp(BBinOpKind, Ident<'a>, Ident<'a>),
    IBinOp(IBinOpKind, Ident<'a>, MaybeConst<Ident<'a>>),
    FUnOp(FUnOpKind, Ident<'a>),
    FBinOp(FBinOpKind, Ident<'a>, Ident<'a>),
    FTerOp(FTerOpKind, Ident<'a>, Ident<'a>, Ident<'a>),
    If(IfExpr<VarDef<'a>, Ident<'a>, Box<Self>>),
    Let(VarDef<'a>, Box<Self>, Box<Self>),
    Var(VarDef<'a>),
    Tuple(Vec<MaybeConst<VarDef<'a>>>),
    Get(VarDef<'a>, MaybeConst<Ident<'a>>),
    Set(VarDef<'a>, MaybeConst<Ident<'a>>, Ident<'a>),
    ArrayMake(MaybeConst<Ident<'a>>, MaybeConst<VarDef<'a>>),
    PrintInt(MaybeConst<Ident<'a>>),
    Pervasive(ast::Ident<'a>, Vec<Ident<'a>>),
    Loop(Continue<'a>, Box<Self>),
    Continue(Continue<'a>),
    // below are modified from knorm
    GetGlobal(Ident<'a>, MaybeConst<Ident<'a>>),
    SetGlobal(Ident<'a>, MaybeConst<Ident<'a>>, Ident<'a>),
    ApplyDirectly(Label<'a>, Vec<VarDef<'a>>),
}

#[derive(Debug, Clone)]
pub struct FunDef<'a> {
    pub name: VarDef<'a>,
    pub args: Vec<VarDef<'a>>,
    pub captured_vars: Vec<VarDef<'a>>,
    pub body: Box<IrNode<'a>>,
}

#[derive(Debug, Clone)]
pub struct Prog<'a> {
    pub fundefs: Vec<FunDef<'a>>,
    pub toplevel_var_types: HashMap<Ident<'a>, Ty>,
    pub tail_expr: IrNode<'a>,
}

impl<'a> IrNode<'a> {
    pub fn fv<'b>(&'b self) -> HashSet<&'b Ident<'a>> {
        use IrNode::*;
        use MaybeConst::*;
        match self {
            Const(_) | GetGlobal(_, Constant(_)) => HashSet::new(),
            IUnOp(_, x)
            | FUnOp(_, x)
            | GetGlobal(_, Variable(x))
            | SetGlobal(_, Constant(_), x)
            | IBinOp(_, x, Constant(_)) => HashSet::from_iter([x]),
            Get(x, Constant(_)) => HashSet::from_iter([&x.name]),
            IBinOp(_, x, Variable(y)) | BBinOp(_, x, y) | FBinOp(_, x, y) => {
                HashSet::from_iter([x, y])
            }
            Get(x, Variable(y)) | Set(x, Constant(_), y) => HashSet::from_iter([x, y]),
            SetGlobal(_, Variable(x), y) => HashSet::from_iter([x, y]),
            If(IfExpr {
                cond: IfCond::Bin { lhs: x, rhs: y, .. },
                clauses:
                    IfBranch::ThenElse {
                        then_: e1,
                        else_: e2,
                    },
            }) => {
                let h = HashSet::from_iter([x, y]);
                let s1 = e1.fv();
                let s2 = e2.fv();
                &(&h | &s1) | &s2
            }
            If(IfExpr {
                cond: IfCond::Un { lhs: x, .. },
                clauses:
                    IfBranch::ThenElse {
                        then_: e1,
                        else_: e2,
                    },
            }) => {
                let h = HashSet::from_iter([&x.name]);
                let s1 = e1.fv();
                let s2 = e2.fv();
                &(&h | &s1) | &s2
            }
            Let(VarDef { name, ty: _ }, e1, e2) => {
                let s1 = e1.fv();
                let s2 = &e2.fv() - &HashSet::from_iter([name]);
                &s1 | &s2
            }
            Set(x, Variable(y), z) => HashSet::from_iter([x, y, z]),
            FTerOp(_, x, y, z) => HashSet::from_iter([x, y, z]),
            Var(x) => HashSet::from_iter([&x.name]),
            ApplyDirectly(_, xs) => xs.iter().map(|x| &x.name).collect(),
            Tuple(xs) => xs
                .iter()
                .flat_map(MaybeConst::as_variable)
                .map(|v| &v.name)
                .collect(),
            Pervasive(_, xs) => xs.iter().collect(),
            ArrayMake(i1, i2) => [i1.as_ref(), i2.as_deref()]
                .iter()
                .filter_map(MaybeConst::as_variable)
                .cloned()
                .collect(),
            PrintInt(i) => i.as_variable().iter().cloned().collect(),
            Loop(ir_knorm::Continue(_, c), e) => {
                let s0 = c.iter().map(|(x, _)| &x.name).collect();
                let s1 = c.iter().map(|(_, x)| &x.name).collect();
                let s2 = &e.fv() - &s0;
                &s1 | &s2
            }
            Continue(ir_knorm::Continue(_, c)) => c.iter().map(|(_, x)| &x.name).collect(),
        }
    }
}
