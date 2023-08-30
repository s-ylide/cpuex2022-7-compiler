use ir_asm_virtual_ast_isa1st::{BasicBlock, CondBr, Terminator, VAsmFunDef};

/// reorders bb in order to shorten jump distance of CondBr
/// within b-immediate width (12-bit), or j-immediate width (20-bit)
pub fn reorder_bb_shorten_jump(fundef: &mut VAsmFunDef) {
    let mut checked_index = 0;
    loop {
        // this is replacement of address, which cannot be caluculated at this point
        let mut acc_bb_len = 0;
        struct SearchCondBr<L> {
            then_label: L,
            else_label: L,
            from_addr: usize,
            from_index: usize,
        }
        let mut search_target = None;
        let mut then_index_distance = None;
        let mut else_index_distance = None;
        'search: for (index, bb) in fundef.body.iter().enumerate().skip(checked_index) {
            if let Some(SearchCondBr {
                then_label,
                else_label,
                from_addr,
                ..
            }) = search_target
            {
                if then_label == &bb.id {
                    then_index_distance = Some(acc_bb_len - from_addr);
                    if else_index_distance.is_some() {
                        break 'search;
                    }
                }
                if else_label == &bb.id {
                    else_index_distance = Some(acc_bb_len - from_addr);
                    if then_index_distance.is_some() {
                        break 'search;
                    }
                }
            }
            acc_bb_len += bb.len();
            if search_target.is_none() {
                if let Terminator::CondBr(CondBr(.., l1, l2)) = &bb.terminator {
                    search_target = Some(SearchCondBr {
                        then_label: l1,
                        else_label: l2,
                        from_addr: acc_bb_len,
                        from_index: index,
                    });
                }
            }
        }
        let Some(SearchCondBr {
            then_label,
            else_label,
            from_index,
            ..
        }) = search_target else { break; };
        checked_index = from_index + 1;
        let then_distance = then_index_distance.unwrap();
        let else_distance = else_index_distance.unwrap();
        const BIMM_FITS: usize = if cfg!(feature = "isa_2nd") {
            1 << 12
        } else {
            1 << 7
        };
        const JIMM_FITS: usize = if cfg!(feature = "isa_2nd") {
            1 << 21
        } else {
            1 << 16
        };
        if then_distance < JIMM_FITS {
            if else_distance < BIMM_FITS {
                // nothing to do
            } else if else_distance < JIMM_FITS {
                if then_distance < BIMM_FITS {
                    log::debug!("far else `{else_label}` detected; flipping condbr.");
                    fundef
                        .body
                        .get_mut(from_index)
                        .as_mut()
                        .unwrap()
                        .terminator
                        .as_condbr_flip();
                } else {
                    // add jump to else
                    log::debug!("far then `{then_label}` and else `{else_label}` detected.");
                    let else_label = else_label.to_owned();
                    let inserted_new_bb = BasicBlock::just_jumps(else_label);
                    *fundef
                        .body
                        .get_mut(from_index)
                        .as_mut()
                        .unwrap()
                        .terminator
                        .as_condbr_else_mut()
                        .unwrap() = inserted_new_bb.id.clone();
                    fundef.body.insert(from_index + 1, inserted_new_bb);
                    continue;
                }
            } else {
                unimplemented!("else too far")
            }
        } else {
            unimplemented!("then too far")
        }
    }
}
