use std::{
    cmp::Reverse,
    collections::{BTreeMap, HashMap, HashSet},
};

use ir_asm_ast_isa1st::abi;
use ir_asm_virtual_ast_isa1st::{Expr, Stmt, VirtualAsm};
use ordered_float::NotNan;
use typedefs::IdentSymbol;

use crate::usage_of_vars::CollectUsage;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PromotableGlobal {
    /// we want decending ordering by `BTreeMap::iter()`
    use_count: Reverse<usize>,
    pub from: PromoteFrom<IdentSymbol>,
}

#[derive(Debug)]
pub struct PromotedIdent {
    ty: abi::RegKind,
    pub map: HashMap<Option<i32>, HashSet<IdentSymbol>>,
}

impl PromotedIdent {
    fn new(ty: abi::RegKind) -> Self {
        Self {
            ty,
            map: Default::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PromoteFrom<T> {
    Label(T),
    ConstF32(NotNan<f32>),
    ConstInt(i32),
}
use PromoteFrom::*;

/// find alias or constant that can be promoted to register.
pub fn find_register_promotable(
    prog: &VirtualAsm,
    c: &CollectUsage,
) -> (
    BTreeMap<PromotableGlobal, PromotedIdent>,
    BTreeMap<PromotableGlobal, PromotedIdent>,
) {
    let mut promoted_idents: HashMap<PromoteFrom<&IdentSymbol>, PromotedIdent> = prog
        .globals_map
        .values()
        .filter_map(|g| {
            Some((
                Label(g.name.id()),
                PromotedIdent::new(match g.ty.as_array()? {
                    ty::ConcTy::Int => abi::RegKind::Int,
                    ty::ConcTy::Float => abi::RegKind::Float,
                    _ => None?,
                }),
            ))
        })
        .chain(
            prog.float_map
                .values()
                .map(|(l, _)| (Label(l.id()), PromotedIdent::new(abi::RegKind::Float))),
        )
        .collect();
    for l in prog.globals_map.values().flat_map(|g| {
        g.value
            .as_cconst()
            .into_iter()
            .filter_map(|c| c.as_address_of())
    }) {
        promoted_idents.remove(&Label(l.id()));
    }
    for fundef in &prog.fundefs {
        for bb in &fundef.body {
            for instr in &bb.instrs {
                match instr {
                    Stmt::Assign(Some(d), .., Expr::LoadInt(c)) => {
                        promoted_idents
                            .entry(ConstInt(*c))
                            .or_insert(PromotedIdent::new(abi::RegKind::Int))
                            .map
                            .entry(None)
                            .or_default()
                            .insert(*d.id());
                    }
                    Stmt::Assign(Some(d), .., Expr::LoadF32(c)) => {
                        promoted_idents
                            .entry(ConstF32(*c))
                            .or_insert(PromotedIdent::new(abi::RegKind::Float))
                            .map
                            .entry(None)
                            .or_default()
                            .insert(*d.id());
                    }
                    Stmt::Assign(Some(d), .., Expr::LoadFromLabelDisp(None, l, index)) => {
                        if let Some(m) = promoted_idents.get_mut(&Label(l.id())) {
                            m.map.entry(Some(*index)).or_default().insert(*d.id());
                        }
                    }
                    // remove unpromotable labels
                    Stmt::Assign(
                        ..,
                        Expr::LoadLabelAddr(l) | Expr::LoadFromLabelDisp(Some(..), l, ..),
                    )
                    | Stmt::StoreLabelDisp(_, Some(..), l, ..)
                    | Stmt::StoreFLabelDisp(_, Some(..), l, ..) => {
                        promoted_idents.remove(&Label(l.id()));
                    }
                    _ => (),
                }
            }
        }
    }
    use rayon::prelude::*;
    let usage_of_var = c.usage_of_var();
    promoted_idents
        .into_par_iter()
        .filter_map(|(ids, gu)| {
            (!gu.map.is_empty()).then(|| {
                (
                    PromotableGlobal {
                        use_count: Reverse(
                            gu.map
                                .par_iter()
                                .flat_map(|(_, hs)| hs.par_iter().map(|ids| usage_of_var[ids]))
                                .sum(),
                        ),
                        from: match ids {
                            Label(l) => Label(*l),
                            ConstF32(c) => ConstF32(c),
                            ConstInt(c) => ConstInt(c),
                        },
                    },
                    gu,
                )
            })
        })
        .partition_map(|(p, gu)| match &gu.ty {
            abi::RegKind::Int => rayon::iter::Either::Left((p, gu)),
            abi::RegKind::Float => rayon::iter::Either::Right((p, gu)),
        })
}
