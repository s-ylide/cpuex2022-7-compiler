use ir_asm_virtual_ast_isa1st::{builder::discard, Expr, Stmt, VAsmFunDef};

use crate::PathState;

/// removes unused definition.
/// it also removes nop.
pub fn remove_unused_def(fundef: &mut VAsmFunDef, st: &mut PathState) {
    for bb in &mut fundef.body {
        for instr in &mut bb.instrs {
            if let Stmt::Assign(Some(d), .., e) = instr {
                if !st.usage_of_var.is_used(d) && !e.has_effect() {
                    *instr = discard(Expr::Nop);
                }
            }
        }
        bb.instrs.retain_mut(|instr| {
            let b = matches!(instr, Stmt::Assign(.., Expr::Nop));
            if b {
                st.did_modify()
            }
            !b
        });
    }
}
