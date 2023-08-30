use std::{cell::RefCell, rc::Rc};
use typedefs::{Ident, IdentSymbol, IfBranch, IfCond, IfExpr};
use util::union_find::UnionFind;

use crate::{Continue, IrNode, PathState};

struct RenamingMap<'a, 'b> {
    inner: UnionFind<IdentSymbol, &'b Ident<'a>>,
}

impl<'a, 'b> RenamingMap<'a, 'b> {
    fn new() -> Self {
        Self {
            inner: UnionFind::new(),
        }
    }
    fn insert(&mut self, k: Ident<'a>, v: &'b Ident<'a>) {
        let key1 = k.id();
        if self.inner.get_root_id(key1).is_none() {
            self.inner.make_set(*key1, v);
        }
        let key2 = v.id();
        if self.inner.get_root_id(key2).is_none() {
            self.inner.make_set(*key2, v);
        }
        self.inner.union(key1, key2).unwrap();
    }
    fn rename(&self, ident: &'b mut Ident<'a>, st: &mut PathState) {
        if let Some(renamed) = self.inner.get_root_id(ident.id()) {
            if ident.id() != renamed.id() {
                log::debug!("beta-reduced {ident} <- {renamed}");
                *ident = (*renamed).clone();
                st.did_modify();
            }
        }
    }
}

pub fn beta_convert(node: &mut IrNode, st: &mut PathState) {
    let mut env = RenamingMap::new();
    enum ModifyEnv<'a, 'b> {
        TryBind(&'b Ident<'a>),
        Nop,
    }
    let mut stack: Vec<(Option<&mut IrNode>, ModifyEnv)> = Vec::new();
    use ModifyEnv::*;
    stack.push((Some(node), Nop));

    fn mu<T>(r: &mut Rc<RefCell<T>>) -> Option<&mut T> {
        Some(Rc::get_mut(r).unwrap().get_mut())
    }

    while let Some((node, m)) = stack.pop() {
        if let Some(node) = node {
            match node {
                IrNode::Const(_) => (),
                IrNode::IUnOp(_, i) | IrNode::FUnOp(_, i) => {
                    env.rename(i, st);
                }
                IrNode::Var(i) => {
                    if let TryBind(ident) = m {
                        st.deprecate_var(ident);
                        env.insert(ident.clone(), i);
                    } else {
                        env.rename(i, st);
                    }
                }
                IrNode::BBinOp(_, i1, i2) | IrNode::FBinOp(_, i1, i2) => {
                    env.rename(i1, st);
                    env.rename(i2, st);
                }
                IrNode::FTerOp(_, i1, i2, i3) => {
                    env.rename(i1, st);
                    env.rename(i2, st);
                    env.rename(i3, st);
                }
                IrNode::IBinOp(_, i1, i2) => {
                    env.rename(i1, st);
                    if let Some(i2) = i2.as_variable_mut() {
                        env.rename(i2, st);
                    }
                }
                IrNode::If(IfExpr {
                    cond: IfCond::Bin { lhs, rhs, .. },
                    clauses: IfBranch::ThenElse { then_, else_ },
                }) => {
                    env.rename(lhs, st);
                    env.rename(rhs, st);
                    stack.push((mu(else_), Nop));
                    stack.push((mu(then_), Nop));
                }
                IrNode::If(IfExpr {
                    cond: IfCond::Un { lhs, .. },
                    clauses: IfBranch::ThenElse { then_, else_ },
                }) => {
                    env.rename(lhs, st);
                    stack.push((mu(else_), Nop));
                    stack.push((mu(then_), Nop));
                }
                IrNode::Let(v, e1, e2) => {
                    stack.push((None, Nop));
                    stack.push((mu(e2), Nop));
                    stack.push((mu(e1), TryBind(&v.name)));
                }
                IrNode::LetRec(fundef, e) => {
                    stack.push((mu(e), Nop));
                    stack.push((mu(&mut fundef.body), Nop));
                }
                IrNode::LetTuple(_, i, e) => {
                    env.rename(i, st);
                    stack.push((mu(e), Nop));
                }
                IrNode::Loop(Continue(_, is), e) => {
                    for (_, i) in is.iter_mut() {
                        env.rename(&mut i.name, st);
                    }
                    stack.push((mu(e), Nop));
                }
                IrNode::Continue(Continue(_, is)) => {
                    for (_, i) in is.iter_mut() {
                        env.rename(&mut i.name, st);
                    }
                }
                IrNode::App(i, is) => {
                    env.rename(i, st);
                    for i in is.iter_mut() {
                        env.rename(&mut i.var.name, st);
                    }
                }
                IrNode::Tuple(is) => {
                    for i in is.iter_mut() {
                        if let Some(i) = i.as_variable_mut() {
                            env.rename(&mut i.name, st);
                        }
                    }
                }
                IrNode::Get(i1, i2) => {
                    env.rename(i1, st);
                    if let Some(i2) = i2.as_variable_mut() {
                        env.rename(i2, st);
                    }
                }
                IrNode::Set(i1, i2, i3) => {
                    env.rename(i1, st);
                    if let Some(i2) = i2.as_variable_mut() {
                        env.rename(i2, st);
                    }
                    env.rename(i3, st);
                }
                IrNode::ArrayMake(i1, i2) => {
                    if let Some(i1) = i1.as_variable_mut() {
                        env.rename(i1, st);
                    }
                    if let Some(i2) = i2.as_variable_mut() {
                        env.rename(i2, st);
                    }
                }
                IrNode::Pervasive(_, is) => {
                    for i in is.iter_mut() {
                        env.rename(&mut i.var.name, st);
                    }
                }
                IrNode::PrintInt(i) => {
                    if let Some(i) = i.as_variable_mut() {
                        env.rename(i, st);
                    }
                }
            }
        }
    }
}
