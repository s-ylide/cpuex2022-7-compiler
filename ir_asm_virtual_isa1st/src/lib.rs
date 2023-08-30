#![feature(iter_partition_in_place)]
#![feature(btree_extract_if)]
#![feature(if_let_guard)]
#![feature(map_try_insert)]

mod asm_transform;
mod asmv_transform;
mod branch_imm;
mod cfg;
mod coalesce_jumps;
mod copy_propagation;
mod critical_edges;
mod cssa;
mod exe_transform;
mod liveness;
mod redundant_param;
mod reg_promotable;
mod regalloc;
mod rename;
mod reorder_bb_shorten_jump;
mod scheduling;
mod tail_call;
mod unlinked_bb;
mod unused_def;
mod unused_store;
mod usage_of_vars;

pub use branch_imm::restore_branch_imm;
pub use coalesce_jumps::rec_coalesce_jumps;
pub use copy_propagation::copy_propagation;
pub use critical_edges::split_critical_edges;
pub use cssa::convert_to_cssa;
pub use redundant_param::redundant_param;
pub use reorder_bb_shorten_jump::reorder_bb_shorten_jump;
pub use scheduling::scheduling;
pub use tail_call::tail_call;
pub use unlinked_bb::remove_unlinked_bb;
pub use unused_def::remove_unused_def;
pub use unused_store::remove_unused_store;
pub use usage_of_vars::CollectUsage;
pub use usage_of_vars::Collectable;

pub use asm_transform::asm_transform;
pub use asmv_transform::asmv_transform;
pub use exe_transform::exe_transform;

use ir_asm_ast_isa1st::abi::{FRegId, RegId};
pub use ir_asm_virtual_ast_isa1st::VirtualAsm;
use std::{
    collections::HashMap,
    fmt::{Display, Write},
    hash::Hash,
};
use typedefs::IdentSymbol;

pub(crate) type Range = bitvec::vec::BitVec;

pub(crate) struct RangeView<'a, Key: 'a> {
    ranges: Vec<(Key, &'a Range)>,
    len: Option<usize>,
}

impl<Key> RangeView<'_, Key> {
    fn sort(&mut self) {
        self.ranges.sort_by_key(|(_, bv)| bv.leading_zeros());
    }
}

impl<'a, Key> RangeView<'a, &'a Key> {
    pub(crate) fn new(ranges: impl IntoIterator<Item = &'a (Key, Range)>, len: usize) -> Self {
        let ranges = ranges.into_iter().map(|(a, b)| (a, b)).collect();
        let mut s = Self {
            ranges,
            len: Some(len),
        };
        s.sort();
        s
    }
}

impl<'a> RangeView<'a, usize> {
    #[allow(unused)]
    pub(crate) fn from_ranges(ranges: impl IntoIterator<Item = &'a Range>) -> Self {
        let ranges = ranges.into_iter().enumerate().collect();
        let mut s = Self { ranges, len: None };
        s.sort();
        s
    }
}

impl<Key: Display + Eq + Hash> Display for RangeView<'_, Key> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.ranges.is_empty() {
            return Ok(());
        }
        let mut width = 5;
        let keys: Vec<_> = self
            .ranges
            .iter()
            .map(|(var, _)| {
                let s = format!("{var}");
                let len = s.chars().count();
                if width < len {
                    width = len;
                }
                s
            })
            .collect();
        write!(f, "{:width$} | ", "print")?;
        let len = self.len.unwrap_or(self.ranges.first().unwrap().1.len() / 2);
        for point in 0..len {
            let n = point % 100;
            write!(f, " {n:02}")?
        }
        writeln!(f)?;
        write!(f, "{:width$} | ", "key")?;
        for _ in 0..len {
            write!(f, " EL")?
        }
        writeln!(f)?;
        for (key, (_, range)) in keys.into_iter().zip(&self.ranges) {
            write!(f, "{key:width$} | ")?;
            let mut prev = false;
            for point in 0..len {
                f.write_char(if prev { '-' } else { ' ' })?;
                let b = range[2 * point];
                f.write_char(if b { '-' } else { ' ' })?;
                let b = range[1 + 2 * point];
                f.write_char(if b { '-' } else { ' ' })?;
                prev = b;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

#[derive(Default)]
pub struct PathState {
    modified: bool,
    pub usage_of_var: CollectUsage,
}

impl PathState {
    /// returns whether the node has room for further optimization
    pub fn modified(&self) -> bool {
        self.modified
    }
    pub fn clear_modified(&mut self) {
        self.modified = false;
    }
    pub fn clear_usage(&mut self) {
        self.usage_of_var.clear()
    }
    pub(crate) fn did_modify(&mut self) {
        self.modified = true;
    }
    pub fn usage_of_var(&self) -> &HashMap<IdentSymbol, usize> {
        self.usage_of_var.usage_of_var()
    }
}
