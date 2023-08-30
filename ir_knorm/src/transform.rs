use ast::{
    BinOpKind, ConstKind, Expr, ExprKind, FBinOpKind, FUnOpKind, IUnOpKind, LetKind, TerOpKind,
    UnOpKind,
};
use std::{cell::RefCell, rc::Rc};
use ty::{CTy, ConcTy, Ty};
use typedefs::{
    CanbeConst, Ident, IfBinFKind, IfBinKind, IfBranch, IfCond, IfExpr, IfUnFKind, IfUnIKind,
    IfUnKind, MaybeConst, VarDef,
};

use crate::{FunDef, IrNode};

/// represents a chain element of let.
pub struct LetChainElem<'a>(VarDef<'a>, Rc<RefCell<IrNode<'a>>>);

/// defer creating tree-structure to avoid recursion
pub fn end_chain_with<'a>(
    chain: impl DoubleEndedIterator<Item = LetChainElem<'a>>,
    last: IrNode<'a>,
) -> IrNode<'a> {
    chain.into_iter().rfold(last, |acc, e| match e {
        LetChainElem(a, b) => IrNode::Let(a, b, Rc::new(RefCell::new(acc))),
    })
}

pub fn insert_let_flat<'a>(
    x: Ident<'a>,
    ty: Ty,
    node: Rc<RefCell<IrNode<'a>>>,
) -> (LetChainElem<'a>, VarDef<'a>) {
    let vd = VarDef { name: x, ty };
    (LetChainElem(vd.clone(), node), vd)
}

pub fn knorm_transform(e: Expr) -> IrNode {
    use IrNode::*;
    fn r<T>(value: T) -> Rc<RefCell<T>> {
        Rc::new(RefCell::new(value))
    }

    let mut stack: Vec<(Box<Expr>, Rc<RefCell<IrNode>>)> = Vec::new();
    let ret = r(Default::default());
    stack.push((Box::new(e), Rc::clone(&ret)));

    while let Some((node, ret)) = stack.pop() {
        let ast::Typed {
            item: span::Spanned {
                item: expr,
                span: _,
            },
            ty: _,
        } = *node;
        macro_rules! insert_let {
            ($e:ident => $node:ident: $ty:pat) => {
                insert_let!(_ @ $e => $node: $ty);
                let $e = Ident::new();
            };
            (_ @ $e:ident => $node:ident: $ty:pat) => {
                let $node = r(Default::default());
                let $ty = $e.ty.as_ref().unwrap().clone();
                stack.push(($e, $node.clone()));
            };
        }
        macro_rules! get_rr {
            ($e:ident => $node:ident) => {
                let e = $e;
                let $node = r(Default::default());
                stack.push((e, $node.clone()));
            };
            ($e:ident) => {
                get_rr!($e => $e)
            };
        }
        macro_rules! ir_knorm {
            (in $t:expr) => {
                r($t)
            };
            (in let $($t:tt)*) => {
                r(ir_knorm!(let $($t)*))
            };
            (let $x:ident $($t:tt)*) => {{
                insert_let!($x => node: ty);
                Let(
                    VarDef {
                        name: $x.clone(),
                        ty,
                    },
                    node,
                    ir_knorm!($($t)*),
                )
            }};
            (let* $x:ident $($t:tt)*) => {{
                insert_let!($x => node: ty);
                let name = $x;
                let $x = VarDef {
                    name,
                    ty,
                };
                Let(
                    $x.clone(),
                    node,
                    ir_knorm!($($t)*),
                )
            }};
        }

        *ret.borrow_mut() = match expr {
            ExprKind::Const(ConstKind::Bool(b)) => Const(ConstKind::Int(b as i32)),
            ExprKind::Const(c) => Const(c),
            ExprKind::UnOp(UnOpKind::Not, e) => {
                ir_knorm! {
                    let e in IUnOp(IUnOpKind::Not, e)
                }
            }
            ExprKind::UnOp(UnOpKind::Neg, e) => {
                ir_knorm! {
                    let e in IUnOp(IUnOpKind::Neg, e)
                }
            }
            ExprKind::BinOp(BinOpKind::IBinOp(op), e1, e2) => {
                ir_knorm! {
                    let e1 in
                    let e2 in
                    IBinOp(op, e1, MaybeConst::Variable(e2))
                }
            }
            ExprKind::UnOp(UnOpKind::FNeg, e) => {
                ir_knorm! {
                    let e in FUnOp(FUnOpKind::Fneg, e)
                }
            }
            ExprKind::UnOp(UnOpKind::Fiszero, e) => {
                ir_knorm! {
                    let e in FUnOp(FUnOpKind::Fiszero, e)
                }
            }
            ExprKind::UnOp(UnOpKind::Fispos, e) => {
                ir_knorm! {
                    let e in FUnOp(FUnOpKind::Fispos, e)
                }
            }
            ExprKind::UnOp(UnOpKind::Fisneg, e) => {
                ir_knorm! {
                    let e in FUnOp(FUnOpKind::Fisneg, e)
                }
            }
            ExprKind::BinOp(BinOpKind::FBinOp(op), e1, e2) => {
                ir_knorm! {
                    let e1 in
                    let e2 in
                    FBinOp(op, e1, e2)
                }
            }
            ExprKind::BinOp(BinOpKind::BBinOp(op), e1, e2) => {
                ir_knorm! {
                    let e1 in
                    let e2 in
                    BBinOp(op, e1, e2)
                }
            }
            ExprKind::TerOp(TerOpKind::FTerOp(op), e1, e2, e3) => {
                ir_knorm! {
                    let e1 in
                    let e2 in
                    let e3 in
                    FTerOp(op, e1, e2, e3)
                }
            }
            ExprKind::If(e1, e3, e4) => 'v: {
                use UnOpKind::*;
                if let ExprKind::BinOp(BinOpKind::BBinOp(op), e1, e2) = e1.item.item {
                    get_rr!(e4);
                    get_rr!(e3);
                    break 'v ir_knorm! {
                        let* e1 in
                        let e2 in
                        If(IfExpr {
                            cond: IfCond::Bin { op: IfBinKind::I(op.into()), lhs: e1, rhs: e2 },
                            clauses: IfBranch::ThenElse { then_: e3, else_: e4 },
                        })
                    };
                } else if let ExprKind::BinOp(BinOpKind::FBinOp(FBinOpKind::Fless), e1, e2) =
                    e1.item.item
                {
                    get_rr!(e4);
                    get_rr!(e3);
                    break 'v ir_knorm! {
                        let* e1 in
                        let e2 in
                        If(IfExpr {
                            cond: IfCond::Bin { op: IfBinKind::F(IfBinFKind::Flt), lhs: e1, rhs: e2 },
                            clauses: IfBranch::ThenElse { then_: e3, else_: e4 },
                        })
                    };
                } else if let ExprKind::UnOp(u @ (Fiszero | Fispos | Fisneg), e1) = e1.item.item {
                    get_rr!(e4);
                    get_rr!(e3);
                    let kind = match u {
                        Fiszero => IfUnFKind::Feqz,
                        Fispos => IfUnFKind::Fgtz,
                        Fisneg => IfUnFKind::Fltz,
                        _ => unreachable!(),
                    };
                    break 'v ir_knorm! {
                        let* e1 in
                        If(IfExpr {
                            cond: IfCond::Un { op: IfUnKind::F(kind), lhs: e1 },
                            clauses: IfBranch::ThenElse { then_: e3, else_: e4 },
                        })
                    };
                }
                get_rr!(e4);
                get_rr!(e3);
                ir_knorm! {
                    let* e1 in
                    If(IfExpr {
                        cond: IfCond::Un { op: IfUnKind::I(IfUnIKind::Nez), lhs: e1 },
                        clauses: IfBranch::ThenElse { then_: e3, else_: e4 },
                    })
                }
            }
            ExprKind::Let(LetKind::LetVar(ast::VarDef { name, ty }, e1, e2)) => {
                get_rr!(e2);
                get_rr!(e1);
                let name = Ident::Source(name);
                Let(VarDef { name, ty }, e1, e2)
            }
            ExprKind::Var(x) => {
                let vd = VarDef {
                    name: Ident::Source(x.item),
                    ty: x.ty.unwrap(),
                };
                IrNode::Var(vd)
            }
            ExprKind::Let(LetKind::LetRec(fundef, following)) => {
                let ast::FunDef {
                    var: ast::VarDef { name, ty },
                    args,
                    body,
                    ret_ty: _,
                } = fundef;
                get_rr!(following);
                get_rr!(body);
                let args: Vec<_> = args.into_iter().map(VarDef::from).collect();
                let name = Ident::Source(name);
                LetRec(
                    FunDef {
                        var: VarDef { name, ty },
                        args,
                        body,
                    },
                    following,
                )
            }
            ExprKind::App(e1, e2s) => {
                let (chain, mut xs): (Vec<_>, Vec<_>) = e2s
                    .into_iter()
                    .map(|e2| {
                        let e2 = Box::new(e2);
                        insert_let!(e2 => node: ty);
                        let (le, vd) = insert_let_flat(e2, ty, node);
                        (le, CanbeConst::new(vd))
                    })
                    .unzip();
                if let ExprKind::LibFun(x, _) = &***e1 {
                    end_chain_with(
                        chain.into_iter(),
                        if *x == "print_int" {
                            IrNode::PrintInt(MaybeConst::Variable(
                                std::mem::take(&mut xs[0]).var.name,
                            ))
                        } else {
                            log::debug!("call of `{x}`");
                            IrNode::Pervasive(x, xs)
                        },
                    )
                } else {
                    insert_let!(e1 => node1: ty1);
                    match ty1.as_concty().unwrap() {
                        ConcTy::Fun(..) => end_chain_with(
                            chain.into_iter(),
                            Let(
                                VarDef {
                                    name: e1.clone(),
                                    ty: ty1,
                                },
                                node1,
                                r(IrNode::App(e1, xs)),
                            ),
                        ),
                        _ => unreachable!("in this case type inference must be failed"),
                    }
                }
            }
            ExprKind::Tuple(es) => {
                let (chain, xs): (Vec<_>, Vec<_>) = es
                    .into_iter()
                    .map(|e| {
                        let e = Box::new(e);
                        insert_let!(e => node: ty);
                        let (le, vd) = insert_let_flat(e, ty, node);
                        (le, MaybeConst::Variable(vd))
                    })
                    .unzip();
                end_chain_with(chain.into_iter(), IrNode::Tuple(xs))
            }
            ExprKind::Let(LetKind::LetTuple(vds, e1, e2)) => {
                get_rr!(e2);
                let vds: Vec<_> = vds.into_iter().map(VarDef::from).collect();
                ir_knorm! {
                    let* e1 in
                    LetTuple(vds, e1, e2)
                }
            }
            ExprKind::ArrayMake(e1, e2) => {
                ir_knorm! {
                    let e1 in
                    let* e2 in
                    ArrayMake(MaybeConst::Variable(e1), MaybeConst::Variable(e2))
                }
            }
            ExprKind::Get(e1, e2) => {
                ir_knorm! {
                    let* e1 in
                    let e2 in
                    Get(e1, MaybeConst::Variable(e2))
                }
            }
            ExprKind::Set(e1, e2, e3) => {
                ir_knorm! {
                    let* e1 in
                    let e2 in
                    let* e3 in
                    Set(e1, MaybeConst::Variable(e2), e3)
                }
            }
            ExprKind::Then(e1, e2) => {
                get_rr!(e2);
                get_rr!(e1);
                Let(
                    VarDef {
                        name: Ident::uniq_name("_"),
                        ty: Ty::C(CTy::Unit),
                    },
                    e1,
                    e2,
                )
            }
            ExprKind::PrintInt(e) => {
                ir_knorm! {
                    let e in
                    PrintInt(MaybeConst::Variable(e))
                }
            }
            ExprKind::LibFun(x, t) => {
                panic!("library function {x}: {t} is not allowed to be treated as a variable")
            }
        }
    }
    ret.take()
}
