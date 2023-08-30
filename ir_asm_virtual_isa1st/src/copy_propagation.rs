use crate::rename::*;
use ir_asm_ast_isa1st::abi::{FRegId, RegId};
use ir_asm_virtual_ast_isa1st::{Expr, FVReg, IVReg, IorF, Stmt, VAsmFunDef};

use crate::PathState;

/// propagate copies.
///
/// does not compute across basic blocks.
pub fn copy_propagation(fundef: &mut VAsmFunDef, st: &mut PathState) {
    let mut rename_i: RenamingMap<RegId, IVReg> = RenamingMap::new();
    let mut rename_f: RenamingMap<FRegId, FVReg> = RenamingMap::new();
    for bb in &mut fundef.body {
        use IorF::*;
        for instr in bb.instrs.iter_mut() {
            match instr {
                Stmt::Assign(Some(I(d)), _, Expr::Mov(pv)) => {
                    rename_i.insert(d, pv.to_owned());
                }
                Stmt::Assign(Some(F(d)), _, Expr::MovF(pv)) => {
                    rename_f.insert(d, pv.to_owned());
                }
                _ => (),
            }
        }
        rename_bb(bb, &rename_i, &rename_f, st);
        rename_i.clear_var_map();
        rename_f.clear_var_map();
    }
}
