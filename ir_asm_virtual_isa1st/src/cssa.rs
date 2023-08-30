use std::collections::HashMap;

use ir_asm_virtual_ast_isa1st::{
    builder, BlockParamDef, BrWithParamRef, BrWithParamRefMut, FVReg, IVReg, Stmt, VAsmFunDef,
};
use multimap::MultiMap;
use typedefs::IdentSymbol;

/// convert back to CSSA form.
pub fn convert_to_cssa(fundef: &mut VAsmFunDef) {
    struct RenamePredecessor<'a> {
        renamed_param: BlockParamDef<IVReg<'a>, FVReg<'a>>,
    }

    let mut params_dst: MultiMap<IdentSymbol, IdentSymbol> = MultiMap::new();

    for bb in &fundef.body {
        if let Some(BrWithParamRef(l, p)) = bb.terminator.as_paramed_br() {
            if !p.is_empty() {
                // add reversed edge
                params_dst.insert(*l.id(), *bb.id.id());
            }
        }
    }

    let mut params_src: HashMap<IdentSymbol, RenamePredecessor> = HashMap::new();

    for bb in &mut fundef.body {
        if let Some(srcs) = params_dst.get_vec(&bb.id) {
            if !srcs.is_empty() {
                for new in bb.block_param.iter_mut() {
                    let old = new.name.clone();
                    new.name.update();
                    bb.instrs.push_front(Stmt::Assign(
                        Some(old),
                        new.ty.clone(),
                        builder::cp_from(new.name.clone()),
                    ));
                }
                for src in srcs {
                    params_src.insert(
                        *src,
                        RenamePredecessor {
                            renamed_param: bb.block_param.to_owned(),
                        },
                    );
                }
            }
        }
    }
    for bb in &mut fundef.body {
        if let Some(RenamePredecessor { renamed_param }) = params_src.get(&bb.id) {
            let BrWithParamRefMut(_, param) = bb.terminator.as_mut_paramed_br().unwrap();
            for (ba, renamed) in param.iter_mut().zip(renamed_param.to_owned()) {
                ba.param = renamed;
                let old = ba.rhs().clone();
                ba.rhs_mut().update();
                bb.instrs.push_back(Stmt::Assign(
                    Some(ba.rhs().clone()),
                    ba.param.ty.clone(),
                    builder::cp_from(old),
                ))
            }
        }
    }
}
