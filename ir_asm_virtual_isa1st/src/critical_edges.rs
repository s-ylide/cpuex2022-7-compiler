use std::collections::HashSet;

use ir_asm_virtual_ast_isa1st::{BasicBlock, BrWithOptParamRefMut, Branch, Terminator, VAsmFunDef};
use typedefs::Label;

use crate::cfg::Cfg;

/// remove critical edges.
pub fn split_critical_edges(fundef: &mut VAsmFunDef) {
    let critical_edges: HashSet<_> = Cfg::from_fundef(fundef)
        .critical_edges()
        .map(|(u, v)| (*u.id(), *v.id()))
        .collect();

    if critical_edges.is_empty() {
        return;
    }
    let mut checked_index = 0;
    'l: loop {
        let mut insertion = None;
        'search: for (index, bb) in fundef.body.iter_mut().enumerate().skip(checked_index) {
            for BrWithOptParamRefMut(v, param) in bb.terminator.as_mut_br() {
                if critical_edges.contains(&(*bb.id.id(), *v.id())) {
                    let inserted = Label::name("inserted");
                    let mut dest = inserted.clone();
                    std::mem::swap(v, &mut dest);
                    insertion = Some((
                        index + 1,
                        inserted,
                        dest,
                        std::mem::take(param.unwrap_or(&mut Vec::new())),
                    ));
                    break 'search;
                }
            }
        }
        if let Some((insert_on, inserted, dest, param)) = insertion {
            log::debug!("splitted critical edge; inserted {inserted}.");
            checked_index = insert_on;
            let term = Terminator::Branch(Branch(dest, param));
            let inserted_new_bb = BasicBlock::only_terminator(inserted, term);
            fundef.body.insert(checked_index, inserted_new_bb);
        } else {
            break 'l;
        }
    }
}
