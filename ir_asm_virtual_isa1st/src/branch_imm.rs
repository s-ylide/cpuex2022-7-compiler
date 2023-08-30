use std::{collections::HashMap, mem};

use ir_asm_virtual_ast_isa1st::{CondBr, CondBrKind, Expr, IorF, Stmt, SymbOrImm, VAsmFunDef};
use typedefs::IdentSymbol;

/// restore branch immediate (2nd ISA)
pub fn restore_branch_imm(fundef: &mut VAsmFunDef) {
    let mut const_map: HashMap<IdentSymbol, i32> = HashMap::new();
    for bb in &mut fundef.body {
        for instr in &mut bb.instrs {
            if let Stmt::Assign(Some(IorF::I(name)), .., Expr::LoadInt(i)) = instr {
                if p_instr_loadable(*i) {
                    const_map.insert(*name.id(), *i);
                }
            }
        }
        if let Some(CondBr(kind, ..)) = bb.terminator.as_mut_condbr() {
            match kind {
                CondBrKind::IfBin(.., SymbOrImm::Imm(_)) => (),
                CondBrKind::IfBin(k, i1, r) => {
                    if let Some(&c1) = const_map.get(i1) {
                        let SymbOrImm::Sym(i2) = r else {
                            unreachable!()
                        };
                        mem::swap(i1, i2);
                        *r = SymbOrImm::Imm(c1);
                        *k = k.flipped_arg();
                    } else {
                        let SymbOrImm::Sym(i2) = r else {
                            unreachable!()
                        };
                        if let Some(&c2) = const_map.get(i2) {
                            *r = SymbOrImm::Imm(c2);
                        }
                    }
                }
                _ => (),
            }
        }
    }
}

fn p_instr_loadable(imm: i32) -> bool {
    imm.abs() < (1 << 5)
}
