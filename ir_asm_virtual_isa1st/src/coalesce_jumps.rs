use std::collections::{HashMap, HashSet};

#[allow(unused)]
use ast::{ConstKind, FBinOpKind, FUnOpKind, IBinOpKind, IUnOpKind};
use ir_asm_virtual_ast_isa1st::{
    Branch, CondBr, CondBrKind, Expr, FVReg, IVReg, IorF, PhysOrVirt, Stmt, StmtList, SymbOrImm,
    Terminator, VAsmFunDef,
};

#[allow(unused)]
use typedefs::{IdentSymbol, IfBinFKind, IfBinIKind, IfUnIKind, Label};

use crate::{
    cfg::Cfg,
    rename::{rename_bb, RenamingMap},
    PathState,
};

pub fn rec_coalesce_jumps(fundef: &mut VAsmFunDef, st: &mut PathState) {
    let empty_bb_terms: HashMap<_, _> = fundef
        .body
        .iter()
        // skip entry bb
        .skip(1)
        .filter_map(|bb| {
            if bb.instrs.is_empty() {
                Some((bb.id.clone(), bb.clone()))
            } else {
                None
            }
        })
        .collect();
    let exit_bbs: HashMap<_, _> = fundef
        .body
        .iter()
        .filter_map(|bb| {
            if bb.terminator.is_exit() {
                Some((bb.id.clone(), bb.clone()))
            } else {
                None
            }
        })
        .collect();
    let back_edge_dsts: HashSet<IdentSymbol> = Cfg::from_fundef(fundef)
        .find_back_edge_dsts()
        .map(|l| *l.id())
        .collect();

    for bb in &mut fundef.body {
        loop {
            match &mut bb.terminator {
                Terminator::Branch(Branch(l, ps)) if let Some(exbb) = exit_bbs.get(l) => {
                    // inline exbb
                    let mut rename_i = RenamingMap::new();
                    let mut rename_f = RenamingMap::new();
                    for bpa in ps {
                        let param = &bpa.param.name;
                        let rhs = bpa.rhs();
                        match (param, rhs) {
                            (IorF::I(k), IorF::I(v)) => {
                                rename_i.insert(k, PhysOrVirt::V(v.clone()));
                            },
                            (IorF::F(k), IorF::F(v)) =>{
                                rename_f.insert(k, PhysOrVirt::V(v.clone()));
                            }
                            _ => unreachable!("type mismatch")
                        }
                    }
                    let mut follows = exbb.clone();
                    for stmt in &mut follows.instrs {
                        if let Stmt::Assign(Some(d), ..) = stmt {
                            match d {
                                IorF::I(d) => {
                                    let k = d.to_owned();
                                    d.update();
                                    rename_i.insert(&k, PhysOrVirt::V(d.to_owned()));
                                }
                                IorF::F(d) => {
                                    let k = d.to_owned();
                                    d.update();
                                    rename_f.insert(&k, PhysOrVirt::V(d.to_owned()));
                                }
                            }
                        }
                    }
                    rename_bb(&mut follows, &rename_i, &rename_f, &mut Default::default());
                    bb.instrs.append(&mut follows.instrs);
                    bb.terminator = follows.terminator;
                    st.did_modify();
                    continue;
                }
                Terminator::Branch(Branch(l, ps)) if ps.len() == 1 => {
                    if back_edge_dsts.contains(l) {
                        break;
                    }
                    let p = ps.first_mut().unwrap();
                    if let Some(ebb) = empty_bb_terms.get(l) {
                        let is_once = st.usage_of_var.is_used_once(&p.param.name);
                        match &ebb.terminator {
                            Terminator::Branch(Branch(ll, pp))
                                if pp.len() == 1
                                    && pp.first().unwrap().rhs() == &p.param.name
                                    && is_once =>
                            {
                                *l = ll.to_owned();
                                p.param = pp.first().unwrap().param.to_owned();
                                st.did_modify();
                                continue;
                            }
                            Terminator::CondBr(CondBr(CondBrKind::IfUn(op, lhs), l1, l2))
                                if p.param.name.as_i() == Some(lhs) && is_once =>
                            {
                                bb.terminator = Terminator::CondBr(CondBr(
                                    CondBrKind::IfUn(
                                        op.to_owned(),
                                        p.rhs().as_i().unwrap().to_owned(),
                                    ),
                                    l1.to_owned(),
                                    l2.to_owned(),
                                ));
                                st.did_modify();
                                continue;
                            }
                            Terminator::CondBr(CondBr(CondBrKind::IfUnF(op, PhysOrVirt::V(lhs)), l1, l2))
                                if p.param.name.as_f() == Some(lhs) && is_once =>
                            {
                                bb.terminator = Terminator::CondBr(CondBr(
                                    CondBrKind::IfUnF(
                                        op.to_owned(),
                                        PhysOrVirt::V(p.rhs().as_f().unwrap().to_owned()),
                                    ),
                                    l1.to_owned(),
                                    l2.to_owned(),
                                ));
                                st.did_modify();
                                continue;
                            }
                            Terminator::Ret(..) => {
                                bb.terminator = Terminator::Ret(p.rhs().to_owned());
                                st.did_modify();
                            }
                            Terminator::TailCall(l, is, fs) => {
                                let (is, fs) = match (&p.param.name, p.rhs()) {
                                    (IorF::I(from), IorF::I(into)) => (
                                        is.iter()
                                            .map(|i| {
                                                if i == from {
                                                    into.to_owned()
                                                } else {
                                                    i.to_owned()
                                                }
                                            })
                                            .collect(),
                                        fs.to_owned(),
                                    ),
                                    (IorF::F(from), IorF::F(into)) => (
                                        is.to_owned(),
                                        fs.iter()
                                            .map(|f| {
                                                if f == from {
                                                    into.to_owned()
                                                } else {
                                                    f.to_owned()
                                                }
                                            })
                                            .collect(),
                                    ),
                                    _ => unreachable!(),
                                };
                                bb.terminator = Terminator::TailCall(l.to_owned(), is, fs);
                                st.did_modify();
                            }
                            _ => (),
                        }
                    }
                }
                Terminator::Branch(Branch(l, em)) if em.is_empty() => {
                    if back_edge_dsts.contains(l) {
                        break;
                    }
                    if let Some(ebb) = empty_bb_terms.get(l) {
                        bb.terminator = ebb.terminator.to_owned();
                        st.did_modify();
                        continue;
                    }
                }
                Terminator::CondBr(CondBr(c, l1, l2)) => {
                    loop {
                        if back_edge_dsts.contains(l1) {
                            break;
                        }
                        if let Some(ebb) = empty_bb_terms.get(l1) {
                            if let Some(l) = ebb.terminator.as_simple_br() {
                                *l1 = l.to_owned();
                                st.did_modify();
                                continue;
                            }
                        }
                        break;
                    }
                    loop {
                        if back_edge_dsts.contains(l2) {
                            break;
                        }
                        if let Some(ebb) = empty_bb_terms.get(l2) {
                            if let Some(l) = ebb.terminator.as_simple_br() {
                                *l2 = l.to_owned();
                                st.did_modify();
                                continue;
                            }
                        }
                        break;
                    }
                    if let CondBrKind::IfUn(k @ (IfUnIKind::Nez | IfUnIKind::Eqz), b) = c {
                        if st.usage_of_var.is_used_once(b) {
                            fn get_def_expr<'a, 'b>(
                                stmts: &'b StmtList<Label<'a>, IVReg<'a>, FVReg<'a>>,
                                b: &IVReg<'a>,
                            ) -> Option<&'b Expr<Label<'a>, IVReg<'a>, FVReg<'a>>>
                            {
                                for stmt in stmts.iter().rev() {
                                    match stmt {
                                        Stmt::Assign(Some(d), _, e) if b.id() == d.id() => {
                                            if !e.has_effect() {
                                                return Some(e);
                                            } else {
                                                return None;
                                            }
                                        }
                                        Stmt::Assign(_, _, e) if !e.has_effect() => (),
                                        _ => break,
                                    }
                                }
                                None
                            }
                            if let Some(e) = get_def_expr(&bb.instrs, b) {
                                if let Some(ConstKind::Int(i)) = e.const_eval() {
                                    bb.terminator = if k.eval(i) {
                                        Terminator::Branch(Branch(l1.to_owned(), Vec::new()))
                                    } else {
                                        Terminator::Branch(Branch(l2.to_owned(), Vec::new()))
                                    };
                                    continue;
                                }
                                use CondBrKind::*;
                                use FBinOpKind::*;
                                use FUnOpKind::*;
                                #[cfg(feature = "isa_2nd")]
                                use IBinOpKind::*;
                                use IUnOpKind::*;
                                let mut c = match e {
                                    Expr::IUnOp(Not, i) => IfUn(IfUnIKind::Eqz, i.to_owned()),
                                    Expr::FUnOp(k @ (Fiszero | Fispos | Fisneg), f) => {
                                        IfUnF((*k).try_into().unwrap(), f.to_owned())
                                    }
                                    Expr::BBinOp(k, i1, i2) => IfBin(
                                        k.to_owned().into(),
                                        i1.to_owned(),
                                        SymbOrImm::Sym(i2.to_owned()),
                                    ),
                                    #[cfg(feature = "isa_2nd")]
                                    Expr::IBinOp(Xor, i1, i2) => {
                                        IfBin(IfBinIKind::Xor, i1.to_owned(), i2.to_owned())
                                    }
                                    Expr::FBinOp(Fless, f1, f2) => {
                                        IfBinF(IfBinFKind::Flt, f1.to_owned(), f2.to_owned())
                                    }
                                    _ => break,
                                };
                                if matches!(k, IfUnIKind::Eqz) {
                                    c.filp_cond();
                                }
                                bb.terminator =
                                    Terminator::CondBr(CondBr(c, l1.to_owned(), l2.to_owned()));
                                st.did_modify();
                                break;
                            }
                        }
                    }
                }
                _ => (),
            }
            break;
        }
    }
}
