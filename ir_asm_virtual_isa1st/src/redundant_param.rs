use std::collections::{HashMap, HashSet};

use ir_asm_virtual_ast_isa1st::{
    BrWithParamRef, BrWithParamRefMut, Expr, IorF, LetBound, PhysOrVirt, Stmt, VAsmFunDef,
};
use typedefs::IdentSymbol;

use crate::PathState;

/// removes redundant param definition.
pub fn redundant_param(fundef: &mut VAsmFunDef, st: &mut PathState) {
    enum Search {
        FoundOnce(IdentSymbol),
        FoundMany,
    }
    use Search::*;

    let mut red_params_dst: HashMap<IdentSymbol, Search> = HashMap::new();

    for bb in &fundef.body {
        if let Some(BrWithParamRef(l, p)) = bb.terminator.as_paramed_br() {
            if p.len() == 1 {
                red_params_dst
                    .entry(*l.id())
                    .and_modify(|e| *e = FoundMany)
                    .or_insert(FoundOnce(*bb.id.id()));
            }
        }
    }

    let mut red_params_src: HashSet<IdentSymbol> = HashSet::new();

    for bb in &mut fundef.body {
        if let Some(FoundOnce(src)) = red_params_dst.get(&bb.id) {
            red_params_src.insert(*src);
            bb.block_param.clear();
            st.did_modify();
        }
    }
    for bb in &mut fundef.body {
        if red_params_src.contains(&bb.id) {
            let BrWithParamRefMut(_, param) = bb.terminator.as_mut_paramed_br().unwrap();
            let assigns = std::mem::take(param);
            bb.instrs.extend(assigns.into_iter().map(|a| {
                let (rhs, LetBound { name, ty }) = a.into_inner();
                Stmt::Assign(
                    Some(name),
                    ty,
                    match rhs {
                        IorF::I(id) => Expr::Mov(PhysOrVirt::V(id)),
                        IorF::F(id) => Expr::MovF(PhysOrVirt::V(id)),
                    },
                )
            }))
        }
    }
}
