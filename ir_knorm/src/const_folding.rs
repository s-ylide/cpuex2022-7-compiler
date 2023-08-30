use std::{cell::RefCell, collections::HashMap, rc::Rc, mem};

use ast::{ConstKind, IBinOpKind};
use ordered_float::NotNan;
use ty::{Ty, CTy};
use typedefs::{Ident, IfBinKind, IfUnKind, MaybeConst, VarDef, CanbeConst, IfExpr, IfCond, IfBranch};

use crate::{IrNode, PathState};

type ConstMap<'a, 'b> = HashMap<&'b Ident<'a>, ConstKind>;

pub fn const_folding(node: &mut IrNode, st: &mut PathState) {
    enum ModifyEnv<'a, 'b> {
        TryBind(&'b Ident<'a>),
        Nop,
    }
    use ConstKind::*;
    use MaybeConst::*;
    use ModifyEnv::*;
    let mut stack: Vec<(Option<&mut IrNode>, ModifyEnv)> = Vec::new();
    stack.push((Some(node), Nop));
    let mut env_const = ConstMap::new();

    fn mu<T>(r: &mut Rc<RefCell<T>>) -> Option<&mut T> {
        Some(Rc::get_mut(r).unwrap().get_mut())
    }

    fn rr<T>(v: T) -> Rc<RefCell<T>> {
        Rc::new(RefCell::new(v))
    }

    while let Some((node, m)) = stack.pop() {
        if let Some(node) = node {
            match node {
                IrNode::Const(c) => {
                    if let TryBind(ident) = m {
                        env_const.insert(ident, *c);
                    }
                }
                IrNode::IUnOp(op, i) => {
                    if let Some(c) = env_const.get(i) {
                        let i = *c.as_int().unwrap();
                        let c = op.eval(i);
                        *node = IrNode::Const(c);
                        st.did_modify();
                        if let TryBind(ident) = m {
                            env_const.insert(ident, c);
                        }
                    }
                }
                IrNode::BBinOp(op, i1, i2) => {
                    if let (Some(c1), Some(c2)) = (env_const.get(i1), env_const.get(i2)) {
                        let lhs = *c1.as_int().unwrap();
                        let rhs = *c2.as_int().unwrap();
                        let c = op.eval(lhs, rhs);
                        *node = IrNode::Const(Bool(c));
                        st.did_modify();
                        if let TryBind(ident) = m {
                            env_const.insert(ident, Bool(c));
                        }
                    }
                }
                IrNode::IBinOp(IBinOpKind::Min | IBinOpKind::Max, ..) => (),
                IrNode::IBinOp(op, i1, op2) => match op2 {
                    Variable(i2) => match (env_const.get(i1), env_const.get(i2)) {
                        (Some(c1), Some(c2)) => {
                            let lhs = *c1.as_int().unwrap();
                            let rhs = *c2.as_int().unwrap();
                            let c = op.eval(lhs, rhs);
                            *node = IrNode::Const(Int(c));
                            st.did_modify();
                            if let TryBind(ident) = m {
                                env_const.insert(ident, Int(c));
                            }
                        }
                        (_, Some(c2)) => {
                            *op2 = Constant(*c2);
                            st.did_modify();
                        }
                        (Some(c1), _) => {
                            match op {
                                IBinOpKind::Add | IBinOpKind::Mul | IBinOpKind::Xor => {
                                    *i1 = i2.clone();
                                    *op2 = Constant(*c1);
                                    st.did_modify();
                                }
                                _ => (),
                            }
                        }
                        _ => (),
                    },
                    Constant(c2) => {
                        if let Some(c1) = env_const.get(i1) {
                            let lhs = *c1.as_int().unwrap();
                            let rhs = *c2.as_int().unwrap();
                            let c = op.eval(lhs, rhs);
                            *node = IrNode::Const(Int(c));
                            st.did_modify();
                            if let TryBind(ident) = m {
                                env_const.insert(ident, Int(c));
                            }
                        } else {
                            let c2 = *c2.as_int().unwrap();
                            let ones = c2.count_ones();
                            if ones == 1 {
                                let p = c2.ilog2() as i32;
                                if let IBinOpKind::Mul = op {
                                    *op = IBinOpKind::Sll;
                                    *op2 = Constant(Int(p));
                                    st.did_modify();
                                    log::debug!("replaced mul by 2^n with shift.");
                                } else if let IBinOpKind::Div = op {
                                    *op = IBinOpKind::Srl;
                                    *op2 = Constant(Int(p));
                                    st.did_modify();
                                    log::debug!("replaced div by 2^n with shift.");
                                }
                            } else if ones == 0 {
                                match op {
                                    IBinOpKind::Mul => {
                                        *node = IrNode::Const(Int(0));
                                        st.did_modify();
                                    }
                                    IBinOpKind::Div => panic!("division by zero"),
                                    IBinOpKind::Add
                                    | IBinOpKind::Sub
                                    | IBinOpKind::Sll
                                    | IBinOpKind::Srl
                                    | IBinOpKind::Xor
                                    | IBinOpKind::Or => {
                                        *node = IrNode::Var(VarDef { name: i1.clone(), ty: Ty::C(CTy::Int) });
                                        st.did_modify();
                                    }
                                    IBinOpKind::Min | IBinOpKind::Max => (),
                                }
                            }
                        }
                    }
                },
                IrNode::FUnOp(op, i) => {
                    if let Some(c) = env_const.get(i) {
                        let f = *c.as_float().unwrap();
                        let c = op.eval(f);
                        *node = IrNode::Const(c);
                        st.did_modify();
                        if let TryBind(ident) = m {
                            env_const.insert(ident, c);
                        }
                    }
                }
                IrNode::FBinOp(op, i1, i2) if let (Some(c1), Some(c2)) = (env_const.get(i1), env_const.get(i2)) => {
                    let lhs = *c1.as_float().unwrap();
                    let rhs = *c2.as_float().unwrap();
                    let c = op.eval(lhs, rhs);
                    *node = IrNode::Const(c);
                    st.did_modify();
                    if let TryBind(ident) = m {
                        env_const.insert(ident, c);
                    }
                }
                IrNode::FBinOp(op, i1, i2) if let Some(c2) = env_const.get(i2) => {
                    let rhs = *c2.as_float().unwrap();
                    if rhs == 2.0 && matches!(op, ast::FBinOpKind::FMul) {
                        *node = IrNode::FBinOp(ast::FBinOpKind::FAdd, i1.to_owned(), std::mem::take(i1));
                        st.did_modify();
                    } else if rhs == 1.0 && matches!(op, ast::FBinOpKind::FMul) {
                        *node = IrNode::Var(VarDef { name: std::mem::take(i1), ty: Ty::C(CTy::Float) });
                        st.did_modify();
                    } else if matches!(op, ast::FBinOpKind::FDiv) {
                        let inv = Ident::ubiq_name("inv");
                        *node = IrNode::Let(
                            VarDef { name: inv.clone(), ty: Ty::C(CTy::Float) },
                            rr(IrNode::Const(Float(NotNan::new(1.0 / rhs).unwrap()))),
                            rr(IrNode::FBinOp(ast::FBinOpKind::FMul, std::mem::take(i1), inv)));
                        st.did_modify();
                    }
                }
                IrNode::FBinOp(op, i1, i2) if let Some(c1) = env_const.get(i1) => {
                    let lhs = *c1.as_float().unwrap();
                    if lhs == 1.0 && matches!(op, ast::FBinOpKind::FDiv) {
                        *node = IrNode::FUnOp(ast::FUnOpKind::Finv, std::mem::take(i2));
                        st.did_modify();
                    }
                    else if lhs == 2.0 && matches!(op, ast::FBinOpKind::FMul) {
                        *node = IrNode::FBinOp(ast::FBinOpKind::FAdd, i2.to_owned(), std::mem::take(i2));
                        st.did_modify();
                    }
                    else if lhs == 1.0 && matches!(op, ast::FBinOpKind::FMul) {
                        *node = IrNode::Var(VarDef { name: std::mem::take(i2), ty: Ty::C(CTy::Float) });
                        st.did_modify();
                    }
                }
                IrNode::If(IfExpr {
                    cond:
                        IfCond::Bin {
                            op: IfBinKind::I(op),
                            lhs, rhs,
                        },
                    clauses:
                        IfBranch::ThenElse {
                            then_,
                            else_,
                        },
                }) if let (Some(c1), Some(c2)) = (env_const.get(&lhs.name), env_const.get(rhs)) => {
                    let lhs = *c1.as_int().unwrap();
                    let rhs = *c2.as_int().unwrap();
                    if op.eval(lhs, rhs) {
                        *node = then_.take();
                        st.did_modify();
                        stack.push((Some(node), m));
                    } else {
                        *node = else_.take();
                        st.did_modify();
                        stack.push((Some(node), m));
                    }
                }
                IrNode::If(IfExpr {
                    cond:
                        IfCond::Bin {
                            op: IfBinKind::F(op),
                            lhs, rhs,
                        },
                    clauses:
                        IfBranch::ThenElse {
                            then_,
                            else_,
                        },
                }) if let (Some(c1), Some(c2)) = (env_const.get(&lhs.name), env_const.get(rhs)) => {
                    let lhs = *c1.as_float().unwrap();
                    let rhs = *c2.as_float().unwrap();
                    if op.eval(lhs, rhs) {
                        *node = then_.take();
                        st.did_modify();
                        stack.push((Some(node), m));
                    } else {
                        *node = else_.take();
                        st.did_modify();
                        stack.push((Some(node), m));
                    }
                }
                IrNode::If(IfExpr {
                    cond:
                        IfCond::Un {
                            op: IfUnKind::I(op),
                            lhs,
                        },
                    clauses:
                        IfBranch::ThenElse {
                            then_,
                            else_,
                        },
                }) if let Some(c) = env_const.get(&lhs.name) => {
                    let i = match c {
                        Bool(b) => *b as i32,
                        Int(i) => *i,
                        _ => unreachable!()
                    };
                    if op.eval(i) {
                        *node = then_.take();
                        st.did_modify();
                        stack.push((Some(node), m));
                    } else {
                        *node = else_.take();
                        st.did_modify();
                        stack.push((Some(node), m));
                    }
                }
                IrNode::If(IfExpr {
                    cond:
                        IfCond::Un {
                            op: IfUnKind::F(op),
                            lhs,
                        },
                    clauses:
                        IfBranch::ThenElse {
                            then_,
                            else_,
                        },
                }) if let Some(c) = env_const.get(&lhs.name) => {
                    let i = *c.as_float().unwrap();
                    if op.eval(i) {
                        *node = then_.take();
                        st.did_modify();
                        stack.push((Some(node), m));
                    } else {
                        *node = else_.take();
                        st.did_modify();
                        stack.push((Some(node), m));
                    }
                }
                IrNode::If(IfExpr {
                    cond:
                        IfCond::Bin {
                            op,
                            lhs: VarDef { name: lhs, ty }, rhs,
                        },
                    clauses: IfBranch::ThenElse {
                        then_,
                        else_,
                    },
                })
                    if env_const.get(lhs).and_then(ConstKind::as_zero).is_some() => {
                    *node = IrNode::If(IfExpr {
                        cond:
                            IfCond::Un {
                                op: op.fix_lhs_z(),
                                lhs: VarDef {
                                    name: mem::take(rhs), ty: ty.clone()
                                },
                            },
                        clauses: IfBranch::ThenElse {
                            then_: mem::take(then_),
                            else_: mem::take(else_),
                        },
                    });
                    st.did_modify();
                    stack.push((Some(node), m));
                }
                IrNode::If(IfExpr {
                    cond:
                        IfCond::Bin {
                            op,
                            lhs, rhs,
                        },
                    clauses: IfBranch::ThenElse {
                        then_,
                        else_,
                    },
                })
                    if env_const.get(rhs).and_then(ConstKind::as_zero).is_some() => {
                    *node = IrNode::If(IfExpr {
                        cond:
                            IfCond::Un {
                                op: op.fix_rhs_z(),
                                lhs: mem::take(lhs),
                            },
                        clauses: IfBranch::ThenElse {
                            then_: mem::take(then_),
                            else_: mem::take(else_),
                        },
                    });
                    st.did_modify();
                    stack.push((Some(node), m));
                }
                IrNode::If(IfExpr {
                    clauses:
                        IfBranch::ThenElse {
                            then_: e1,
                            else_: e2,
                        },
                    ..
                }) => {
                    stack.push((mu(e1), Nop));
                    stack.push((mu(e2), Nop));
                }
                IrNode::Let(VarDef { name, .. }, e1, e2) => {
                    stack.push((mu(e2), m));
                    stack.push((mu(e1), TryBind(name)));
                }
                IrNode::LetRec(fundef, e) => {
                    stack.push((mu(e), m));
                    stack.push((mu(&mut fundef.body), Nop));
                }
                IrNode::LetTuple(_, _, e) => {
                    stack.push((mu(e), m));
                }
                IrNode::Loop(_, e) => {
                    stack.push((mu(e), Nop));
                }
                IrNode::Var(..) => {}
                IrNode::ArrayMake(Constant(Int(0)), _) => {
                    *node = IrNode::Const(ConstKind::Int(0));
                    st.did_modify();
                    log::debug!("replaced zero-length array with null pointer.");
                }
                IrNode::ArrayMake(i1, i2) => {
                    if let Variable(var) = i1 {
                        if let Some(c) = env_const.get(var) {
                            *i1 = Constant(*c);
                            st.did_modify();
                        }
                    }
                    if let Variable(var) = i2 {
                        if let Some(c) = env_const.get(&var.name) {
                            *i2 = Constant(*c);
                            st.did_modify();
                        }
                    }
                }
                IrNode::Set(arr, Constant(index), i) => {
                    if let Some(o) = st.get_elim_static_mut(*arr.id(), *index.as_int().unwrap()) {
                        if o.is_none() {
                            if let Some(c) = env_const.get(&i.name) {
                                log::debug!("`{arr}.({index})` can be replaced with constant `{c}`.");
                                *o = Some(*c);
                            }
                        }
                        if o.is_some() {
                            log::debug!("replaced `{arr}.({index})` with constant.");
                            *node = IrNode::Const(ConstKind::Unit);
                            st.did_modify();
                        }
                    }
                }
                IrNode::Get(arr, Constant(index)) => {
                    if let Some(o) = st.get_elim_static_mut(*arr.id(), *index.as_int().unwrap()) {
                        if let Some(c) = o.as_mut() {
                            let c = *c;
                            *node = IrNode::Const(c);
                            st.did_modify();
                        } 
                    }
                }
                IrNode::Get(_, i) | IrNode::Set(_, i, _) | IrNode::PrintInt(i) => {
                    if let Variable(var) = i {
                        if let Some(c) = env_const.get(var) {
                            *i = Constant(*c);
                            st.did_modify();
                        }
                    }
                }
                IrNode::Tuple(t) => {
                    for i in t {
                        if let Variable(var) = i {
                            if let Some(c) = env_const.get(&var.name) {
                                *i = Constant(*c);
                                st.did_modify();
                            }
                        }
                    }
                }
                IrNode::Pervasive(f, args) => {
                    for CanbeConst{ var, value } in args.iter_mut() {
                        if let Some(c) = env_const.get(&var.name) {
                           *value = Some(*c);
                        }
                    }
                    if let "float_of_int" = f as &str {
                        let cc = args.first().unwrap();
                        if let Some(v) = cc.value {
                            let c = v.as_int().unwrap();
                            *node = IrNode::Const(Float(NotNan::new(*c as f32).unwrap()));
                            st.did_modify();
                        }
                    }
                }
                _ => ()
            }
        }
    }
}
