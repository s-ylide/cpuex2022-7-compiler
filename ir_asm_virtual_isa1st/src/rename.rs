use std::{collections::HashMap, hash::Hash};

use ir_asm_ast_isa1st::abi::{FRegId, RegId};
use ir_asm_virtual_ast_isa1st::{
    BasicBlock, Branch, CondBr, CondBrKind, Expr, IdSymb, IorF, PhysOrVirt, Stmt, SymbOrImm,
    Terminator,
};
use typedefs::IdentSymbol;
use util::union_find::UnionFind;

use crate::PathState;

pub struct RenamingMap<PR, VR> {
    inner: UnionFind<IdentSymbol, VR>,
    inner_p: HashMap<IdentSymbol, PR>,
}

impl<PR: Clone, VR: Hash + Eq + Clone + IdSymb> RenamingMap<PR, VR> {
    pub fn new() -> Self {
        Self {
            inner: UnionFind::new(),
            inner_p: HashMap::new(),
        }
    }
    pub fn clear_var_map(&mut self) {
        self.inner.clear();
    }
    pub fn insert(&mut self, k: &VR, v: PhysOrVirt<PR, VR>) {
        match v {
            PhysOrVirt::P(p) => {
                self.inner_p.insert(*k.id(), p);
            }
            PhysOrVirt::V(v) => {
                let key1 = k;
                if self.inner.get_root_id(key1.id()).is_none() {
                    self.inner.make_set(*key1.id(), v.clone());
                }
                let key2 = *v.id();
                if self.inner.get_root_id(&key2).is_none() {
                    self.inner.make_set(key2, v);
                }
                self.inner.union(key1.id(), &key2).unwrap();
            }
        }
    }
    pub fn rename(&self, pv: &mut PhysOrVirt<PR, VR>, st: &mut PathState) {
        if let PhysOrVirt::V(ident) = pv {
            if let Some(renamed) = self.inner_p.get(ident.id()) {
                *pv = PhysOrVirt::P(renamed.clone());
                st.did_modify();
            } else {
                self.rename_ident(ident, st);
            }
        }
    }
    pub fn rename_ident(&self, ident: &mut VR, st: &mut PathState) {
        if let Some(renamed) = self.inner.get_root_id(ident.id()) {
            if ident != &renamed {
                *ident = renamed.clone();
                st.did_modify();
            }
        }
    }
}

pub fn rename_bb<L, IV: Hash + Eq + Clone + IdSymb, FV: Hash + Eq + Clone + IdSymb>(
    bb: &mut BasicBlock<L, IV, FV>,
    rename_i: &RenamingMap<RegId, IV>,
    rename_f: &RenamingMap<FRegId, FV>,
    st: &mut PathState,
) {
    use IorF::*;
    for instr in bb.instrs.iter_mut() {
        match instr {
            Stmt::Assign(.., e) => match e {
                Expr::Load(i, _) | Expr::Mov(i) | Expr::LoadFromLabelDisp(Some(i), ..) => {
                    if let Some(i) = i.as_mut_v() {
                        rename_i.rename_ident(i, st);
                    }
                }
                Expr::IUnOp(_, i) => {
                    rename_i.rename_ident(i, st);
                }
                Expr::MovF(f) => {
                    if let Some(f) = f.as_mut_v() {
                        rename_f.rename_ident(f, st);
                    }
                }
                Expr::FUnOp(_, f) => {
                    rename_f.rename(f, st);
                }
                Expr::BBinOp(_, i1, i2) => {
                    rename_i.rename_ident(i1, st);
                    rename_i.rename_ident(i2, st);
                }
                Expr::IBinOp(_, i1, i2) => {
                    rename_i.rename_ident(i1, st);
                    if let SymbOrImm::Sym(i2) = i2 {
                        rename_i.rename_ident(i2, st);
                    }
                }
                Expr::FBinOp(_, f1, f2) => {
                    rename_f.rename(f1, st);
                    rename_f.rename(f2, st);
                }
                Expr::FTerOp(_, f1, f2, f3) => {
                    rename_f.rename(f1, st);
                    rename_f.rename(f2, st);
                    rename_f.rename(f3, st);
                }
                Expr::CallDirectly(_, is, fs) | Expr::Intrinsic(_, is, fs) => {
                    for i in is {
                        rename_i.rename_ident(i, st);
                    }
                    for f in fs {
                        rename_f.rename_ident(f, st);
                    }
                }
                Expr::Nop
                | Expr::LoadInt(_)
                | Expr::LoadF32(_)
                | Expr::LoadLabelAddr(_)
                | Expr::LoadFromLabelDisp(None, ..) => (),
            },
            Stmt::Store(pv1, pv2, _) => {
                if let Some(i) = pv1.as_mut_v() {
                    rename_i.rename_ident(i, st);
                }
                if let Some(i) = pv2.as_mut_v() {
                    rename_i.rename_ident(i, st);
                }
            }
            Stmt::StoreF(pv1, pv2, _) => {
                rename_f.rename(pv1, st);
                if let Some(i) = pv2.as_mut_v() {
                    rename_i.rename_ident(i, st);
                }
            }
            Stmt::StoreLabelDisp(i, i1, _, _) => {
                if let Some(i) = i1.as_mut().and_then(|i| i.as_mut_v()) {
                    rename_i.rename_ident(i, st);
                }
                if let Some(i) = i.as_mut_v() {
                    rename_i.rename_ident(i, st);
                }
            }
            Stmt::StoreFLabelDisp(f, i1, _, _) => {
                if let Some(i) = i1.as_mut().and_then(|i| i.as_mut_v()) {
                    rename_i.rename_ident(i, st);
                }
                rename_f.rename(f, st);
            }
            _ => (),
        }
    }
    match &mut bb.terminator {
        Terminator::Exit | Terminator::End => (),
        Terminator::Ret(I(u)) => {
            rename_i.rename_ident(u, st);
        }
        Terminator::Ret(F(u)) => {
            rename_f.rename_ident(u, st);
        }
        Terminator::Branch(Branch(_, us)) => {
            for i in us {
                match i.rhs_mut() {
                    I(ident) => {
                        rename_i.rename_ident(ident, st);
                    }
                    F(ident) => {
                        rename_f.rename_ident(ident, st);
                    }
                }
            }
        }
        Terminator::CondBr(CondBr(c, ..)) => match c {
            CondBrKind::IfBin(_, u1, u2, ..) => {
                rename_i.rename_ident(u1, st);
                if let Some(u2) = u2.as_mut_ident() {
                    rename_i.rename_ident(u2, st);
                }
            }
            CondBrKind::IfBinF(_, u1, u2, ..) => {
                rename_f.rename(u1, st);
                rename_f.rename(u2, st);
            }
            CondBrKind::IfUn(_, u, ..) => {
                rename_i.rename_ident(u, st);
            }
            CondBrKind::IfUnF(_, u, ..) => {
                rename_f.rename(u, st);
            }
        },
        Terminator::TailCall(_, is, fs) => {
            for i in is {
                rename_i.rename_ident(i, st);
            }
            for f in fs {
                rename_f.rename_ident(f, st);
            }
        }
    }
}
