use std::collections::HashSet;

use ir_asm_virtual_ast_isa1st::VAsmFunDef;
use typedefs::IdentSymbol;

/// removes unlinked bb.
pub fn remove_unlinked_bb(fundef: &mut VAsmFunDef) {
    let mut dst: HashSet<IdentSymbol> = HashSet::new();
    dst.insert(*fundef.body.front().unwrap().id.id());
    for bb in &fundef.body {
        dst.extend(bb.terminator.dests().map(|l| *l.id()))
    }
    fundef.body.retain(|bb| dst.contains(&bb.id));
}
