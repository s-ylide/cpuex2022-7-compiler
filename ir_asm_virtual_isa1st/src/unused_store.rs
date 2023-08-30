use std::collections::HashSet;

use ir_asm_virtual_ast_isa1st::{builder::discard, Expr, PhysOrVirt, Stmt, VAsmFunDef};
use typedefs::IdentSymbol;

use crate::PathState;

/// removes unused value assigned to array with constant index.
/// does not compute across basic blocks.
pub fn remove_unused_store(fundef: &mut VAsmFunDef, st: &mut PathState) {
    for bb in &mut fundef.body {
        let mut array: HashSet<IdentSymbol> = HashSet::new();
        let mut alias: HashSet<(IdentSymbol, i32)> = HashSet::new();
        for instr in bb.instrs.iter_mut().rev() {
            use PhysOrVirt::*;
            match instr {
                Stmt::Assign(.., e) => match e {
                    Expr::Mov(V(a)) => {
                        array.remove(a);
                    }
                    Expr::Load(V(a), i) => {
                        alias.remove(&(***a, *i));
                    }
                    Expr::CallDirectly(_, ints, _) | Expr::Intrinsic(_, ints, _) => {
                        for a in ints {
                            array.remove(a);
                        }
                    }
                    _ => (),
                },
                Stmt::Store(_, V(a), i) | Stmt::StoreF(_, V(a), i) => {
                    if array.contains(a) && alias.contains(&(***a, *i)) {
                        *instr = discard(Expr::Nop);
                        st.did_modify();
                    } else {
                        array.insert(***a);
                        alias.insert((***a, *i));
                    }
                }
                _ => (),
            }
        }
    }
}
