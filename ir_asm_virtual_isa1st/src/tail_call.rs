use ir_asm_virtual_ast_isa1st::{Expr, Stmt, Terminator, VAsmFunDef};

/// notices tail call.
pub fn tail_call(fundef: &mut VAsmFunDef) {
    for bb in &mut fundef.body {
        if let Terminator::Ret(a) = &bb.terminator {
            if let Some(Stmt::Assign(Some(b), _, Expr::CallDirectly(l, is, fs))) =
                bb.instrs.back_mut()
            {
                if a == b {
                    bb.terminator = Terminator::TailCall(
                        std::mem::take(l),
                        std::mem::take(is),
                        std::mem::take(fs),
                    );
                    bb.instrs.pop_back();
                }
            }
        } else if let Terminator::Exit = &bb.terminator {
            if let Some(Stmt::Assign(None, _, Expr::CallDirectly(l, is, fs))) = bb.instrs.back_mut()
            {
                bb.terminator =
                    Terminator::TailCall(std::mem::take(l), std::mem::take(is), std::mem::take(fs));
                bb.instrs.pop_back();
            }
        }
    }
}
