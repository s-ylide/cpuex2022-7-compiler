use crate::{
    liveness::{liveness_analysis, InstrPoint, ProgramPoint},
    reg_promotable::{find_register_promotable, PromotableGlobal, PromoteFrom, PromotedIdent},
    regalloc::{regalloc, LiveRange, RAResult},
    usage_of_vars::CollectUsage,
    Range,
};

#[allow(unused_imports)]
use ast::FTerOpKind;
#[allow(unused_imports)]
use ast::{BBinOpKind, FBinOpKind, FUnOpKind, IBinOpKind, IUnOpKind};
use bitvec::prelude::*;
use ir_asm_ast_isa1st::{abi::*, *};
pub use ir_asm_virtual_ast_isa1st::VirtualAsm;
use ir_asm_virtual_ast_isa1st::{
    AsmFunDef, BasicBlock, BlockParamAssign, Branch, CondBr, CondBrKind, Expr, IntoInner, IorF,
    IorF::*, LetBound, PhysOrVirt::*, Prog, Stmt, StmtList, SymbOrImm, Terminator, VAsmFunDef,
};

use itertools::{Either, Itertools};
use multimap::MultiMap;
use ordered_float::NotNan;
use rayon::prelude::*;
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use typedefs::{Ident, IdentSymbol, IfBinFKind, IfBinIKind, IfUnFKind, IfUnIKind, Label};
use util::resolve_cyclic_assign::{resolve_cyclic_assignment, Mv};

fn replace_vregs<'a, 'fun>(
    f: &'fun VAsmFunDef<'a>,
    RAResult {
        must_save_vars,
        live_range_unions_i,
        live_range_unions_f,
        live_ranges_i,
        live_ranges_f,
        mut restore_right_after,
        bb_param_index,
    }: RAResult<'a, 'fun, Label<'a>>,
    ra2: &FillRAMap,
) -> AsmFunDef<'a> {
    let broken_reg_map: HashMap<Label, (HashSet<RegId>, HashSet<FRegId>)> = HashMap::from_iter([
        (
            Label::raw_name(".create_array_int"),
            (
                HashSet::from_iter([RegId::arg_nth(0), RegId::arg_nth(1), RegId::arg_nth(2)]),
                HashSet::new(),
            ),
        ),
        (
            Label::raw_name(".create_array_float"),
            (
                HashSet::from_iter([RegId::arg_nth(0), RegId::arg_nth(2)]),
                HashSet::from_iter([FRegId::arg_nth(0)]),
            ),
        ),
    ]);
    let mut use_live_range_beginnings: MultiMap<_, _> = live_range_unions_i
        .iter()
        .flat_map(|(reg, uni)| {
            uni.live_range_ids.iter().filter_map(|id| {
                let LiveRange {
                    var,
                    range,
                    is_def_range,
                } = live_ranges_i.get(&id.live_range_id).unwrap();
                if !*is_def_range {
                    Some((range.leading_zeros(), (var, I(**reg))))
                } else {
                    None
                }
            })
        })
        .collect();
    use_live_range_beginnings.extend(live_range_unions_f.iter().flat_map(|(reg, uni)| {
        uni.live_range_ids.iter().filter_map(|id| {
            let LiveRange {
                var,
                range,
                is_def_range,
            } = live_ranges_f.get(&id.live_range_id).unwrap();
            if !*is_def_range {
                Some((range.leading_zeros(), (var, F(**reg))))
            } else {
                None
            }
        })
    }));
    let live_range_env_i: MultiMap<_, _> = live_range_unions_i
        .iter()
        .flat_map(|(reg, uni)| {
            uni.live_range_ids.iter().map(|id| {
                let LiveRange {
                    var,
                    range,
                    is_def_range,
                } = live_ranges_i.get(&id.live_range_id).unwrap();
                (*var, (**reg, range.clone(), *is_def_range))
            })
        })
        .collect();

    let live_range_env_f: MultiMap<_, _> = live_range_unions_f
        .iter()
        .flat_map(|(reg, uni)| {
            uni.live_range_ids.iter().map(|id| {
                let LiveRange {
                    var,
                    range,
                    is_def_range,
                } = live_ranges_f.get(&id.live_range_id).unwrap();
                (*var, (**reg, range.clone(), *is_def_range))
            })
        })
        .collect();
    let mut body: VecDeque<BasicBlock<Label, RegId, FRegId>> =
        VecDeque::with_capacity(f.body.len());
    // increment `program_point` to follow the numbering in liveness analysis.
    // do not confused with `body.len()`
    let mut program_point = ProgramPoint::new();
    let stack_map: HashMap<_, _> = must_save_vars
        .iter()
        .filter(|i| !ra2.mapping_i.contains_key(i) && !ra2.mapping_f.contains_key(i))
        .enumerate()
        .map(|(i, v)| (*v, i as i32))
        .collect();
    let stack_len = stack_map.len() + 1;
    let stack_size = stack_len as i32;
    let mut live_range_env_i_cache: HashMap<&Ident, (&RegId, &Range)> = HashMap::new();
    let mut live_range_env_f_cache: HashMap<&Ident, (&FRegId, &Range)> = HashMap::new();
    macro_rules! index_usedef {
        (Def) => {
            program_point.get_index(Late)
        };
        (Use) => {
            program_point.get_index(Early)
        };
        ([$e:expr]) => {
            $e
        };
    }
    macro_rules! replace_inner {
        (d aif $i:ident) => {
            match $i {
                I(i) => I(replace_inner!(d iv i)),
                F(i) => F(replace_inner!(d fv i)),
            }
        };
        (aif $i:ident) => {
            match $i {
                I(i) => I(replace_inner!(iv i)),
                F(i) => F(replace_inner!(fv i)),
            }
        };
        (d iv $i:ident) => {
            allocated_reg_def!($i.inner_ref())
        };
        (d fv $i:ident) => {
            allocated_freg_def!($i.inner_ref())
        };
        (iv $i:ident) => {
            allocated_reg!(Use: $i.inner_ref())
        };
        (fv $i:ident) => {
            allocated_freg!(Use: $i.inner_ref())
        };
        (ivs $i:ident) => {
            $i.iter().map(|i| replace_inner!(iv i)).collect()
        };
        (fvs $i:ident) => {
            $i.iter().map(|i| replace_inner!(fv i)).collect()
        };
        (ipv $i:ident) => {
            P(match $i {
                V(i) => replace_inner!(iv i),
                P(i) => replace_inner!(i),
            })
        };
        (fpv $i:ident) => {
            P(match $i {
                V(i) => replace_inner!(fv i),
                P(i) => replace_inner!(i),
            })
        };
        (si $i:ident) => {
            match $i {
                Sym(i) => Sym(replace_inner!(iv i)),
                Imm(i) => Imm(replace_inner!(i)),
            }
        };
        ($i:ident) => {
            $i.to_owned()
        };
        (pass $i:ident) => {
            $i
        };
    }
    macro_rules! replace {
        ($variant:path; $($($t:ident)+),* $(,)?) => {
            $variant($(replace_inner!($($t)*)),*)
        };
    }
    use InstrPoint::*;

    let mut args = None;
    let mut fargs = None;
    // the first bb is "entry"
    let mut entry_bb = true;
    for bb in &f.body {
        let mut instrs = StmtList::new();
        macro_rules! allocated_reg_def {
            ($e:expr) => {{
                let var = $e;
                let &reg = get_allocated_range(
                    var,
                    &live_range_env_i,
                    &mut live_range_env_i_cache,
                    index_usedef![Def],
                    &ra2.mapping_i,
                );
                insert_save_if_needed(var, I(reg), &stack_map, &mut instrs);
                reg
            }};
        }
        macro_rules! allocated_reg {
            ($t:tt: $e:expr) => {{
                let var = $e;
                let &reg = get_allocated_range(
                    var,
                    &live_range_env_i,
                    &mut live_range_env_i_cache,
                    index_usedef![$t],
                    &ra2.mapping_i,
                );
                reg
            }};
        }
        macro_rules! allocated_freg_def {
            ($e:expr) => {{
                let var = $e;
                let &reg = get_allocated_range(
                    var,
                    &live_range_env_f,
                    &mut live_range_env_f_cache,
                    index_usedef![Def],
                    &ra2.mapping_f,
                );
                insert_save_if_needed(var, F(reg), &stack_map, &mut instrs);
                reg
            }};
        }
        macro_rules! allocated_freg {
            ($t:tt: $e:expr) => {{
                let var = $e;
                let &reg = get_allocated_range(
                    var,
                    &live_range_env_f,
                    &mut live_range_env_f_cache,
                    index_usedef![$t],
                    &ra2.mapping_f,
                );
                reg
            }};
        }
        if entry_bb {
            allocate_stack(stack_size, &mut instrs);
            save_ra(stack_size, &mut instrs);
            args = Some(
                f.args
                    .iter()
                    .map(|(ivreg, t)| (allocated_reg_def!(ivreg.inner_ref()), t.clone()))
                    .collect(),
            );
            fargs = Some(
                f.fargs
                    .iter()
                    .map(|(fvreg, t)| (allocated_freg_def!(fvreg.inner_ref()), t.clone()))
                    .collect(),
            );
            entry_bb = false;
        }

        let block_param = match &bb.block_param {
            v if v.is_empty() => Vec::new(),
            lbs => {
                program_point.incr();
                lbs.iter()
                    .map(|LetBound { name: iorf, ty: c }| LetBound {
                        name: replace_inner!(d aif iorf),
                        ty: replace_inner!(c),
                    })
                    .collect()
            }
        };
        for instr in &bb.instrs {
            program_point.incr();
            if let Some(regs) = use_live_range_beginnings.remove(&program_point.early()) {
                for (var, reg) in regs {
                    insert_restore(var, reg, &stack_map, &mut instrs);
                }
            }
            use SymbOrImm::*;
            // None for "default", unknown
            let mut broken_reg = None;

            match instr {
                Stmt::IncrABI(r, imm) => {
                    instrs.push_back(Stmt::IncrABI(*r, *imm));
                }
                Stmt::Assign(d, _, u) => {
                    let rd = d.as_ref().map(|a| match a {
                        I(i) => I(allocated_reg!(Def: i.inner_ref())),
                        F(f) => F(allocated_freg!(Def: f.inner_ref())),
                    });
                    let u = match u {
                        Expr::Nop => Expr::Nop,
                        Expr::LoadInt(arg0) => {
                            if let Some(&r) = ra2.prom_map_i.get(&FillRAInit::LoadInt(*arg0)) {
                                Expr::Mov(P(r))
                            } else {
                                replace!(Expr::LoadInt; arg0)
                            }
                        }
                        Expr::LoadF32(arg0) => {
                            if let Some(&r) = ra2.prom_map_f.get(&FillRAInit::LoadF32(*arg0)) {
                                Expr::MovF(P(r))
                            } else if let Some(&r) =
                                ra2.prom_map_f.get(&FillRAInit::LoadF32(-*arg0))
                            {
                                Expr::FUnOp(FUnOpKind::Fneg, P(r))
                            } else {
                                match FConstSource::from_f32(*arg0) {
                                    FConstSource::Value(f) => Expr::LoadF32(f),
                                    FConstSource::MovF(r) => Expr::MovF(P(r)),
                                    FConstSource::Fneg(r) => Expr::FUnOp(FUnOpKind::Fneg, P(r)),
                                }
                            }
                        }
                        Expr::LoadLabelAddr(arg0) => replace!(Expr::LoadLabelAddr; arg0),
                        Expr::Mov(arg0) => replace!(Expr::Mov; ipv arg0),
                        Expr::MovF(arg0) => replace!(Expr::MovF; fpv arg0),
                        Expr::IUnOp(arg0, arg1) => replace!(Expr::IUnOp; arg0, iv arg1),
                        Expr::BBinOp(arg0, arg1, arg2) => {
                            replace!(Expr::BBinOp; arg0, iv arg1, iv arg2)
                        }
                        Expr::IBinOp(arg0, arg1, arg2) => {
                            replace!(Expr::IBinOp; arg0, iv arg1, si arg2)
                        }
                        Expr::FUnOp(arg0, arg1) => replace!(Expr::FUnOp; arg0, fpv arg1),
                        Expr::FBinOp(arg0, arg1, arg2) => {
                            replace!(Expr::FBinOp; arg0, fpv arg1, fpv arg2)
                        }
                        Expr::FTerOp(arg0, arg1, arg2, arg3) => {
                            replace!(Expr::FTerOp; arg0, fpv arg1, fpv arg2, fpv arg3)
                        }
                        Expr::Load(arg0, arg1) => replace!(Expr::Load; ipv arg0, arg1),
                        Expr::LoadFromLabelDisp(arg0, arg1, arg2) => {
                            if let Some(&r) = ra2
                                .prom_map_i
                                .get(&FillRAInit::LoadFromLabelDisp(*arg1.id(), *arg2))
                            {
                                Expr::Mov(P(r))
                            } else if let Some(&fr) = ra2
                                .prom_map_f
                                .get(&FillRAInit::LoadFromLabelDisp(*arg1.id(), *arg2))
                            {
                                Expr::MovF(P(fr))
                            } else {
                                let rs1 = arg0.as_ref().map(|rs1| replace_inner!(ipv rs1));
                                replace!(Expr::LoadFromLabelDisp; pass rs1, arg1, arg2)
                            }
                        }
                        Expr::CallDirectly(arg0, arg1, arg2) => {
                            broken_reg = broken_reg_map.get(arg0);
                            replace!(Expr::CallDirectly; arg0, ivs arg1, fvs arg2)
                        }
                        Expr::Intrinsic(arg0, arg1, arg2) => {
                            replace!(Expr::Intrinsic; arg0, ivs arg1, fvs arg2)
                        }
                    };
                    instrs.push_back(Stmt::Assign(rd.clone(), None, u));
                    if let Some(x) = &d {
                        let var = match x {
                            I(i) => i.inner_ref(),
                            F(f) => f.inner_ref(),
                        };
                        insert_save_if_needed(var, rd.unwrap(), &stack_map, &mut instrs);
                    }
                }
                Stmt::Store(rs2, rs1, imm) => {
                    let s = replace!(Stmt::Store; ipv rs2, ipv rs1, imm);
                    instrs.push_back(s);
                }
                Stmt::StoreF(rs2, rs1, imm) => {
                    let s = replace!(Stmt::StoreF; fpv rs2, ipv rs1, imm);
                    instrs.push_back(s);
                }
                Stmt::StoreLabelDisp(rs2, rs1, l, imm) => {
                    if let Some(r) = ra2
                        .prom_map_i
                        .get(&FillRAInit::LoadFromLabelDisp(*l.id(), *imm))
                    {
                        let s = Stmt::Assign(Some(I(*r)), None, replace!(Expr::Mov; ipv rs2));
                        instrs.push_back(s);
                    } else {
                        let rs1 = rs1.as_ref().map(|rs1| replace_inner!(ipv rs1));
                        let s = replace!(Stmt::StoreLabelDisp; ipv rs2, pass rs1, l, imm);
                        instrs.push_back(s);
                    }
                }
                Stmt::StoreFLabelDisp(rs2, rs1, l, imm) => {
                    if let Some(r) = ra2
                        .prom_map_f
                        .get(&FillRAInit::LoadFromLabelDisp(*l.id(), *imm))
                    {
                        let s = Stmt::Assign(Some(F(*r)), None, replace!(Expr::MovF; fpv rs2));
                        instrs.push_back(s);
                    } else {
                        let rs1 = rs1.as_ref().map(|rs1| replace_inner!(ipv rs1));
                        let s = replace!(Stmt::StoreFLabelDisp; fpv rs2, pass rs1, l, imm);
                        instrs.push_back(s);
                    }
                }
            }

            if let Some(vars) = restore_right_after.remove(&program_point) {
                if let Some((i_broken, f_broken)) = broken_reg {
                    for (var, ty) in vars {
                        match ty {
                            abi::RegKind::Int => {
                                let reg = allocated_reg!(Use: var);
                                if i_broken.contains(&reg) {
                                    insert_restore(var, I(reg), &stack_map, &mut instrs);
                                }
                            }
                            abi::RegKind::Float => {
                                let reg = allocated_freg!(Use: var);
                                if f_broken.contains(&reg) {
                                    insert_restore(var, F(reg), &stack_map, &mut instrs);
                                }
                            }
                        };
                    }
                } else {
                    for (var, ty) in vars {
                        match ty {
                            abi::RegKind::Int => {
                                let reg = allocated_reg!(Use: var);
                                insert_restore(var, I(reg), &stack_map, &mut instrs);
                            }
                            abi::RegKind::Float => {
                                let reg = allocated_freg!(Use: var);
                                insert_restore(var, F(reg), &stack_map, &mut instrs);
                            }
                        };
                    }
                }
            }
            if let Some(regs) = use_live_range_beginnings.remove(&program_point.late()) {
                for (var, reg) in regs {
                    insert_restore(var, reg, &stack_map, &mut instrs);
                }
            }
        }
        program_point.incr();
        if let Some(regs) = use_live_range_beginnings.remove(&program_point.early()) {
            for (var, reg) in regs {
                insert_restore(var, reg, &stack_map, &mut instrs);
            }
        }
        let terminator = match &bb.terminator {
            Terminator::End => Terminator::End,
            Terminator::Exit => {
                restore_ra(stack_size, &mut instrs);
                deallocate_stack(stack_size, &mut instrs);
                Terminator::Exit
            }
            Terminator::Ret(u) => {
                restore_ra(stack_size, &mut instrs);
                deallocate_stack(stack_size, &mut instrs);
                replace!(Terminator::Ret; aif u)
            }
            Terminator::Branch(Branch(l, lb)) => {
                let lb = lb
                    .iter()
                    .map(|a| {
                        let pp = bb_param_index[l];
                        let LetBound { name: u, ty } = &a.param;
                        let rhs = a.rhs();
                        let u = match u {
                            I(i) => I(allocated_reg!([pp.late()]: i.inner_ref())),
                            F(f) => F(allocated_freg!([pp.late()]: f.inner_ref())),
                        };
                        let param = LetBound {
                            name: u,
                            ty: ty.clone(),
                        };
                        let rhs = replace_inner!(aif rhs);
                        let mut b = BlockParamAssign::new(param);
                        b.set_rhs(rhs);
                        b
                    })
                    .collect();
                Terminator::Branch(replace!(Branch; l, pass lb))
            }
            Terminator::CondBr(CondBr(cond, then_, else_)) => {
                let cond = match cond {
                    CondBrKind::IfBin(cond, rs1, rs2) => {
                        use SymbOrImm::*;
                        replace!(CondBrKind::IfBin; cond, iv rs1, si rs2)
                    }
                    CondBrKind::IfBinF(cond, rs1, rs2) => {
                        replace!(CondBrKind::IfBinF; cond, fpv rs1, fpv rs2)
                    }
                    CondBrKind::IfUn(cond, rs1) => {
                        replace!(CondBrKind::IfUn; cond, iv rs1)
                    }
                    CondBrKind::IfUnF(cond, rs1) => {
                        replace!(CondBrKind::IfUnF; cond, fpv rs1)
                    }
                };
                Terminator::CondBr(replace!(CondBr; pass cond, then_, else_))
            }
            Terminator::TailCall(l, arg1, arg2) => {
                restore_ra(stack_size, &mut instrs);
                deallocate_stack(stack_size, &mut instrs);
                replace!(Terminator::TailCall; l, ivs arg1, fvs arg2)
            }
        };
        body.push_back(BasicBlock {
            id: bb.id.clone(),
            instrs,
            terminator,
            block_param,
        });
    }
    assert!(use_live_range_beginnings.is_empty());
    assert!(restore_right_after.is_empty(), "{restore_right_after:?}");
    AsmFunDef {
        body,
        args: args.unwrap(),
        fargs: fargs.unwrap(),
        name: f.name.clone(),
        ret: f.ret.clone(),
    }
}

#[inline]
fn allocate_stack<Label>(stack_size: i32, instrs: &mut StmtList<Label, RegId, FRegId>) {
    instrs.push_back(Stmt::IncrABI(REG_SP, -stack_size));
}

#[inline]
fn deallocate_stack<Label>(stack_size: i32, instrs: &mut StmtList<Label, RegId, FRegId>) {
    instrs.push_back(Stmt::IncrABI(REG_SP, stack_size));
}

#[inline]
fn save_ra<Label>(stack_size: i32, instrs: &mut StmtList<Label, RegId, FRegId>) {
    instrs.push_back(Stmt::Store(P(REG_RA), P(REG_SP), stack_size - 1));
}

#[inline]
fn restore_ra<Label>(stack_size: i32, instrs: &mut StmtList<Label, RegId, FRegId>) {
    instrs.push_back(Stmt::Assign(
        Some(I(REG_RA)),
        None,
        Expr::Load(P(REG_SP), stack_size - 1),
    ));
}

#[inline]
fn insert_restore<'a, Label>(
    var: &'a Ident<'a>,
    reg: IorF<RegId, FRegId>,
    stack_map: &HashMap<&'a Ident<'a>, i32>,
    instrs: &mut StmtList<Label, RegId, FRegId>,
) {
    if let Some(&imm) = stack_map.get(var) {
        log::debug!("inserted restore {var}: {reg} <- {imm}(sp)");
        instrs.push_back(Stmt::Assign(Some(reg), None, Expr::Load(P(REG_SP), imm)));
    }
}

#[inline]
fn insert_save_if_needed<'a, Label>(
    var: &'a Ident<'a>,
    reg: IorF<RegId, FRegId>,
    stack_map: &HashMap<&'a Ident<'a>, i32>,
    instrs: &mut StmtList<Label, RegId, FRegId>,
) {
    if let Some(&imm) = stack_map.get(var) {
        let stmt = match reg {
            I(rs2) => Stmt::Store(P(rs2), P(REG_SP), imm),
            F(rs2) => Stmt::StoreF(P(rs2), P(REG_SP), imm),
        };
        log::debug!("inserted save {var}: {reg} -> {imm}(sp)");
        instrs.push_back(stmt);
    }
}

fn get_allocated_range<'a, RegId: Register + 'static>(
    var: &'a Ident<'a>,
    env: &'a MultiMap<&'a Ident<'a>, (RegId, BitVec, bool)>,
    env_cache: &mut HashMap<&'a Ident<'a>, (&'a RegId, &'a BitVec)>,
    index: usize,
    ra2: &'a HashMap<IdentSymbol, RegId>,
) -> &'a RegId {
    if let Some(r) = ra2.get(var) {
        return r;
    };
    match env_cache.get(var) {
        Some((reg, bv)) if bv[index] => reg,
        _ => {
            let v = if let Some(v) = env.get_vec(var) {
                v
            } else {
                log::warn!("variable {var} doesn't exist in env.");
                return RegId::zero();
            };
            match v.iter().find(|(_, bv, _)| bv[index]) {
                Some((reg, bv, _)) => {
                    env_cache.insert(var, (reg, bv));
                    reg
                }
                None => {
                    log::warn!("variable {var} doesn't have ranges at #{index}. is this variable really used?");
                    RegId::zero()
                }
            }
        }
    }
}

/// translate fundef into seq of instruction
fn into_instr<'a>(
    f: AsmFunDef<'a>,
    float_map: &FloatConstMap<Label<'a>>,
) -> TextSegment<Label<'a>> {
    let mut body: TextSegment<Label> = TextSegment::new(Vec::with_capacity(f.body.len()));

    body.label(f.name);

    for assign in
        resolve_cyclic_assignment(f.args.into_iter().enumerate().map(|(i, (actual, _))| {
            let abi = RegId::arg_nth(i);
            Mv(actual, abi)
        }))
    {
        let temp = REG_STASH;
        let Mv(rd, rs) = assign.into_move(temp);
        body.instr(pseudo_i!(Mv rd, rs));
    }
    for assign in
        resolve_cyclic_assignment(f.fargs.into_iter().enumerate().map(|(i, (actual, _))| {
            let abi = FRegId::arg_nth(i);
            Mv(actual, abi)
        }))
    {
        let temp = REG_FSTASH;
        let Mv(rd, rs) = assign.into_move(temp);
        body.instr(pseudo_f!(Fmv rd, rs));
    }
    // the first bb is "entry", which doesn't need to be labeled with "entry"
    let mut entry_bb = true;
    let mut deque = f.body;
    while let Some(bb) = deque.pop_front() {
        if !entry_bb {
            body.label(bb.id);
        } else {
            entry_bb = false;
        }
        fn before_call_fn(body: &mut TextSegment<Label>, args: Vec<RegId>, fargs: Vec<FRegId>) {
            for assign in
                resolve_cyclic_assignment(args.into_iter().enumerate().map(|(i, actual)| {
                    let abi = RegId::arg_nth(i);
                    Mv(abi, actual)
                }))
            {
                let temp = REG_STASH;
                let Mv(rd, rs) = assign.into_move(temp);
                body.instr(pseudo_i!(Mv rd, rs));
            }
            for assign in
                resolve_cyclic_assignment(fargs.into_iter().enumerate().map(|(i, actual)| {
                    let abi = FRegId::arg_nth(i);
                    Mv(abi, actual)
                }))
            {
                let temp = REG_FSTASH;
                let Mv(rd, rs) = assign.into_move(temp);
                body.instr(pseudo_f!(Fmv rd, rs));
            }
        }
        fn call_fn<Label>(body: &mut TextSegment<Label>, f: Label) {
            let f = Offset::Label(f);
            body.instr(pseudo_i!(Jal #f));
        }
        fn call_fn_no_return<Label>(body: &mut TextSegment<Label>, f: Label) {
            let f = Offset::Label(f);
            body.instr(pseudo_i!(J #f));
        }

        const UNREACHABLE_ARM: &str = "typeck must have failed, or arm must be covered";
        for instr in bb.instrs {
            match instr {
                Stmt::IncrABI(rs, imm) => {
                    body.instr(pseudo_i!(Addi rs, rs, imm: imm));
                }
                Stmt::Assign(o, _, e) => match o {
                    Some(I(rd)) => match e {
                        Expr::LoadInt(imm) => {
                            body.instr(pseudo_i!(Li rd, imm: imm));
                        }
                        Expr::LoadLabelAddr(l) => {
                            body.instr(pseudo_i!(LoadLabelAddr rd, .l));
                        }
                        Expr::Mov(rs) => {
                            let rs = rs.inner();
                            if rd != rs {
                                body.instr(pseudo_i!(Mv rd, rs));
                            }
                        }
                        Expr::IUnOp(kind, rs) => {
                            let instr = match kind {
                                IUnOpKind::Not => pseudo_i!(Not rd, rs),
                                #[cfg(not(feature = "isa_2nd"))]
                                IUnOpKind::Neg => pseudo_i!(Neg rd, rs),
                                _ => unreachable!("{UNREACHABLE_ARM}"),
                            };
                            body.instr(instr);
                        }
                        Expr::FUnOp(kind, rs) => {
                            let rs = rs.inner();
                            let instr = match kind {
                                FUnOpKind::Fiszero => pseudo_misc!(Fiszero x[rd], f[rs]),
                                FUnOpKind::Fispos => pseudo_misc!(Fispos x[rd], f[rs]),
                                FUnOpKind::Fisneg => pseudo_misc!(Fisneg x[rd], f[rs]),
                                FUnOpKind::Ftoi => pseudo_misc!(Fftoi x[rd], f[rs]),
                                _ => unreachable!("{UNREACHABLE_ARM}"),
                            };
                            body.instr(instr);
                        }
                        #[allow(warnings)]
                        Expr::BBinOp(kind, rs1, rs2) => {
                            let instr = match kind {
                                #[cfg(not(feature = "isa_2nd"))]
                                BBinOpKind::Lt => pseudo_i!(Slt rd, rs1, rs2),
                                #[cfg(not(feature = "isa_2nd"))]
                                BBinOpKind::Gt => pseudo_i!(Slt rd, rs2, rs1),
                                _ => unimplemented!(
                                    "currently {} operator with arbitrary ident are not supported",
                                    kind.symbol()
                                ),
                            };
                            body.instr(instr);
                        }
                        Expr::IBinOp(kind, rs1, SymbOrImm::Sym(rs2)) => {
                            let instr = match kind {
                                IBinOpKind::Add => pseudo_i!(Add rd, rs1, rs2),
                                #[cfg(not(feature = "isa_2nd"))]
                                IBinOpKind::Sub => pseudo_i!(Sub rd, rs1, rs2),
                                #[cfg(not(feature = "isa_2nd"))]
                                IBinOpKind::Sll => pseudo_i!(Sll rd, rs1, rs2),
                                #[cfg(not(feature = "isa_2nd"))]
                                IBinOpKind::Srl => pseudo_i!(Sra rd, rs1, rs2),
                                IBinOpKind::Xor => pseudo_i!(Xor rd, rs1, rs2),
                                #[cfg(not(feature = "isa_2nd"))]
                                IBinOpKind::Or => pseudo_i!(Or rd, rs1, rs2),
                                #[cfg(feature = "isa_2nd")]
                                IBinOpKind::Min => pseudo_i!(Min rd, rs1, rs2),
                                #[cfg(feature = "isa_2nd")]
                                IBinOpKind::Max => pseudo_i!(Max rd, rs1, rs2),
                                _ => unimplemented!(
                                    "currently {} operator with (ident, ident) are not supported",
                                    kind.symbol()
                                ),
                            };
                            body.instr(instr);
                        }
                        Expr::IBinOp(kind, rs1, SymbOrImm::Imm(imm)) => {
                            let instr = match kind {
                                IBinOpKind::Add => pseudo_i!(Addi rd, rs1, imm: imm),
                                IBinOpKind::Sub => pseudo_i!(Subi rd, rs1, imm: imm),
                                IBinOpKind::Sll => pseudo_i!(Slli rd, rs1, imm: imm),
                                #[cfg(not(feature = "isa_2nd"))]
                                IBinOpKind::Srl => pseudo_i!(Srai rd, rs1, imm: imm),
                                IBinOpKind::Xor => pseudo_i!(Xori rd, rs1, imm: imm),
                                #[cfg(not(feature = "isa_2nd"))]
                                IBinOpKind::Or => pseudo_i!(Ori rd, rs1, imm: imm),
                                _ => unimplemented!(
                                    "currently {} operator with (ident, imm) are not supported",
                                    kind.symbol()
                                ),
                            };
                            body.instr(instr);
                        }
                        Expr::FBinOp(kind, rs1, rs2) => {
                            let rs1 = rs1.inner();
                            let rs2 = rs2.inner();
                            let instr = match kind {
                                FBinOpKind::Fless => {
                                    pseudo_misc!(Flt x[rd], f[rs1], f[rs2])
                                }
                                _ => unreachable!("{UNREACHABLE_ARM}"),
                            };
                            body.instr(instr);
                        }
                        Expr::Load(rs, imm) => {
                            let rs = rs.inner();
                            if rs == REG_SP {
                                body.instr(pseudo_i!(Lw[s] rd, imm(rs)));
                            } else {
                                body.instr(pseudo_i!(Lw[h] rd, imm(rs)));
                            }
                        }
                        Expr::LoadFromLabelDisp(rs1, label, imm) => {
                            let rs1 = rs1.map(|r| r.inner());
                            body.instr(pseudo_i!(Lw rd, imm(.label + rs1)));
                        }
                        Expr::CallDirectly(f, args, fargs) => {
                            before_call_fn(&mut body, args, fargs);
                            call_fn(&mut body, f.clone());
                            if rd != REG_A0 {
                                body.instr(pseudo_i!(Mv rd, REG_A0));
                            }
                        }
                        Expr::Intrinsic(f, _, fargs) => {
                            let mut fargs = fargs.into_iter();
                            let instr = match f.as_str() {
                                "fless" => {
                                    let rs1 = fargs.next().unwrap();
                                    let rs2 = fargs.next().unwrap();
                                    pseudo_misc!(Flt x[rd], f[rs1], f[rs2])
                                }
                                "fiszero" => {
                                    let rs = fargs.next().unwrap();
                                    pseudo_misc!(Fiszero x[rd], f[rs])
                                }
                                "fispos" => {
                                    let rs = fargs.next().unwrap();
                                    pseudo_misc!(Fispos x[rd], f[rs])
                                }
                                "fisneg" => {
                                    let rs = fargs.next().unwrap();
                                    pseudo_misc!(Fisneg x[rd], f[rs])
                                }
                                "int_of_float" => {
                                    let rs = fargs.next().unwrap();
                                    pseudo_misc!(Fftoi x[rd], f[rs])
                                }
                                "read_int" => {
                                    pseudo_i!(Inw rd)
                                }
                                _ => unreachable!(),
                            };
                            body.instr(instr);
                        }
                        _ => unreachable!("{UNREACHABLE_ARM}"),
                    },
                    Some(F(rd)) => match e {
                        Expr::LoadF32(l) => {
                            let l = float_map.get(&l.to_bits()).unwrap().0.clone();
                            body.instr(pseudo_f!(FLoadFromLabel rd, .l));
                        }
                        Expr::MovF(rs) => {
                            let rs = rs.inner();
                            if rd != rs {
                                body.instr(pseudo_f!(Fmv rd, rs));
                            }
                        }
                        Expr::IUnOp(kind, rs) => {
                            let instr = match kind {
                                IUnOpKind::ItoF => pseudo_misc!(Fitof f[rd], x[rs]),
                                _ => unreachable!("{UNREACHABLE_ARM}"),
                            };
                            body.instr(instr);
                        }
                        Expr::FUnOp(kind, rs) => {
                            let rs = rs.inner();
                            let instr = match kind {
                                FUnOpKind::Fneg => pseudo_f!(Fneg rd, rs),
                                FUnOpKind::Floor => pseudo_f!(Ffloor rd, rs),
                                FUnOpKind::Sqrt => pseudo_f!(Fsqrt rd, rs),
                                FUnOpKind::Finv => pseudo_f!(Finv rd, rs),
                                _ => unreachable!("{UNREACHABLE_ARM}"),
                            };
                            body.instr(instr);
                        }
                        Expr::FBinOp(kind, rs1, rs2) => {
                            let rs1 = rs1.inner();
                            let rs2 = rs2.inner();
                            let instr = match kind {
                                FBinOpKind::FAdd => pseudo_f!(Fadd rd, rs1, rs2),
                                FBinOpKind::FSub => pseudo_f!(Fsub rd, rs1, rs2),
                                FBinOpKind::FMul => pseudo_f!(Fmul rd, rs1, rs2),
                                FBinOpKind::FDiv => pseudo_f!(Fdiv rd, rs1, rs2),
                                _ => unreachable!("{UNREACHABLE_ARM}"),
                            };
                            body.instr(instr);
                        }
                        #[cfg(feature = "isa_2nd")]
                        Expr::FTerOp(kind, rs1, rs2, rs3) => {
                            let rs1 = rs1.inner();
                            let rs2 = rs2.inner();
                            let rs3 = rs3.inner();
                            let instr = match kind {
                                FTerOpKind::Fmadd => pseudo_f!(Fmadd rd, rs1, rs2, rs3),
                                FTerOpKind::Fmsub => pseudo_f!(Fmsub rd, rs1, rs2, rs3),
                                FTerOpKind::Fnmadd => pseudo_f!(Fnmadd rd, rs1, rs2, rs3),
                                FTerOpKind::Fnmsub => pseudo_f!(Fnmsub rd, rs1, rs2, rs3),
                            };
                            body.instr(instr);
                        }
                        #[cfg(not(feature = "isa_2nd"))]
                        Expr::FTerOp(..) => unreachable!("{UNREACHABLE_ARM}"),
                        Expr::Load(rs, imm) => {
                            let rs = rs.inner();

                            if rs == REG_SP {
                                body.instr(pseudo_f!(Flw[s] rd, imm(rs)));
                            } else {
                                body.instr(pseudo_f!(Flw[h] rd, imm(rs)));
                            }
                        }
                        Expr::LoadFromLabelDisp(rs1, label, imm) => {
                            let rs1 = rs1.map(|r| r.inner());
                            let label = label.clone();
                            body.instr(pseudo_f!(Flw rd, imm(.label + rs1)));
                        }
                        Expr::CallDirectly(f, args, fargs) => {
                            before_call_fn(&mut body, args, fargs);
                            call_fn(&mut body, f.clone());
                            if rd != REG_FA0 {
                                body.instr(pseudo_f!(Fmv rd, REG_FA0));
                            }
                        }
                        Expr::Intrinsic(f, args, fargs) => {
                            let mut args = args.into_iter();
                            let mut fargs = fargs.into_iter();
                            let instr = match f.as_str() {
                                "sqrt" => {
                                    let rs = fargs.next().unwrap();
                                    pseudo_f!(Fsqrt rd, rs)
                                }
                                "fhalf" => {
                                    let rs = fargs.next().unwrap();
                                    pseudo_f!(Fhalf rd, rs)
                                }
                                "fsgnj" => {
                                    let rs1 = fargs.next().unwrap();
                                    let rs2 = fargs.next().unwrap();
                                    pseudo_f!(Fsgnj rd, rs1, rs2)
                                }
                                "fsgnjx" => {
                                    let rs1 = fargs.next().unwrap();
                                    let rs2 = fargs.next().unwrap();
                                    pseudo_f!(Fsgnjx rd, rs1, rs2)
                                }
                                "fsqr" => {
                                    let rs = fargs.next().unwrap();
                                    pseudo_f!(Fmul rd, rs, rs)
                                }
                                "fabs" => {
                                    let rs = fargs.next().unwrap();
                                    pseudo_f!(Fabs rd, rs)
                                }
                                "fneg" => {
                                    let rs = fargs.next().unwrap();
                                    pseudo_f!(Fneg rd, rs)
                                }
                                "floor" => {
                                    let rs = fargs.next().unwrap();
                                    pseudo_f!(Ffloor rd, rs)
                                }
                                "float_of_int" => {
                                    let rs = args.next().unwrap();
                                    pseudo_misc!(Fitof f[rd], x[rs])
                                }
                                "read_float" => {
                                    pseudo_f!(Finw rd)
                                }
                                _ => unreachable!("{UNREACHABLE_ARM}"),
                            };
                            body.instr(instr);
                        }
                        _ => unreachable!("{UNREACHABLE_ARM}"),
                    },
                    None => match e {
                        Expr::Nop => (),
                        Expr::CallDirectly(f, args, fargs) => {
                            before_call_fn(&mut body, args, fargs);
                            call_fn(&mut body, f);
                        }
                        Expr::Intrinsic(f, args, _) => {
                            let mut args = args.into_iter();
                            let instr = match f.as_str() {
                                "print_char" => {
                                    let rs = args.next().unwrap();
                                    pseudo_i!(Outb rs)
                                }
                                _ => unreachable!("{UNREACHABLE_ARM}"),
                            };
                            body.instr(instr);
                        }
                        _ => unreachable!("{UNREACHABLE_ARM}"),
                    },
                },
                Stmt::Store(rs2, rs1, imm) => {
                    let rs2 = rs2.inner();
                    let rs1 = rs1.inner();
                    if rs1 == REG_SP {
                        body.instr(pseudo_i!(Sw[s] rs2, imm(rs1)));
                    } else {
                        body.instr(pseudo_i!(Sw[h] rs2, imm(rs1)));
                    }
                }
                Stmt::StoreF(rs2, rs1, imm) => {
                    let rs2 = rs2.inner();
                    let rs1 = rs1.inner();
                    if rs1 == REG_SP {
                        body.instr(pseudo_f!(Fsw[s] rs2, imm(rs1)));
                    } else {
                        body.instr(pseudo_f!(Fsw[h] rs2, imm(rs1)));
                    }
                }
                Stmt::StoreLabelDisp(rs2, rs1, l, imm) => {
                    let rs1 = rs1.map(|r| r.inner());
                    let rs2 = rs2.inner();
                    body.instr(pseudo_i!(Sw rs2, imm(.l + rs1)));
                }
                Stmt::StoreFLabelDisp(rs2, rs1, l, imm) => {
                    let rs1 = rs1.map(|r| r.inner());
                    let rs2 = rs2.inner();
                    body.instr(pseudo_f!(Fsw rs2, imm(.l + rs1)));
                }
            }
        }
        match bb.terminator {
            Terminator::End => {
                body.instr(pseudo!(End));
            }
            Terminator::Exit => {
                body.instr(pseudo!(Ret));
            }
            Terminator::Ret(I(rs)) => {
                if REG_A0 != rs {
                    body.instr(pseudo_i!(Mv REG_A0, rs));
                }
                body.instr(pseudo!(Ret));
            }
            Terminator::Ret(F(rs)) => {
                if REG_FA0 != rs {
                    body.instr(pseudo_f!(Fmv REG_FA0, rs));
                }
                body.instr(pseudo!(Ret));
            }
            Terminator::Branch(Branch(l, assigns)) => {
                // reflect phi semantics
                let (i_assigns, f_assigns): (Vec<_>, Vec<_>) =
                    assigns.into_iter().partition_map(|assign| {
                        let (rhs, LetBound { name: param, .. }) = assign.into_inner();
                        match (param, rhs) {
                            (I(param), I(rhs)) => Either::Left(Mv(param, rhs)),
                            (F(param), F(rhs)) => Either::Right(Mv(param, rhs)),
                            _ => unreachable!("?"),
                        }
                    });
                for assign in resolve_cyclic_assignment(i_assigns.into_iter()) {
                    let Mv(rd, rs) = assign.into_move(REG_STASH);
                    body.instr(pseudo_i!(Mv rd, rs));
                }
                for assign in resolve_cyclic_assignment(f_assigns.into_iter()) {
                    let Mv(rd, rs) = assign.into_move(REG_FSTASH);
                    body.instr(pseudo_f!(Fmv rd, rs));
                }
                if !matches!(deque.front(), Some(front) if front.id == l) {
                    let l = Offset::Label(l);
                    body.instr(pseudo_i!(J #l));
                }
            }
            Terminator::CondBr(CondBr(c, then_, else_)) => {
                match c {
                    CondBrKind::IfBin(cond, rs1, SymbOrImm::Sym(rs2)) => {
                        let else_ = Offset::Label(else_);
                        let instr = match cond {
                            IfBinIKind::Eq => pseudo_i!(Bne rs1, rs2, #else_),
                            IfBinIKind::Ne => pseudo_i!(Beq rs1, rs2, #else_),
                            IfBinIKind::Le => pseudo_i!(Bgt rs1, rs2, #else_),
                            IfBinIKind::Gt => pseudo_i!(Ble rs1, rs2, #else_),
                            IfBinIKind::Ge => pseudo_i!(Blt rs1, rs2, #else_),
                            IfBinIKind::Lt => pseudo_i!(Bge rs1, rs2, #else_),
                            #[cfg(feature = "isa_2nd")]
                            IfBinIKind::Xor => pseudo_i!(Bxnor rs1, rs2, #else_),
                            #[cfg(feature = "isa_2nd")]
                            IfBinIKind::Xnor => pseudo_i!(Bxor rs1, rs2, #else_),
                            #[cfg(not(feature = "isa_2nd"))]
                            _ => unreachable!(),
                        };
                        body.instr(instr);
                    }
                    #[cfg(feature = "isa_2nd")]
                    CondBrKind::IfBin(cond, rs1, SymbOrImm::Imm(imm)) => {
                        let else_ = Offset::Label(else_);
                        let instr = match cond {
                            IfBinIKind::Eq => pseudo_i!(Bnei rs1, imm: imm, #else_),
                            IfBinIKind::Ne => pseudo_i!(Beqi rs1, imm: imm, #else_),
                            IfBinIKind::Le => pseudo_i!(Bgti rs1, imm: imm, #else_),
                            IfBinIKind::Gt => pseudo_i!(Blei rs1, imm: imm, #else_),
                            IfBinIKind::Ge => pseudo_i!(Blti rs1, imm: imm, #else_),
                            IfBinIKind::Lt => pseudo_i!(Bgei rs1, imm: imm, #else_),
                            _ => unimplemented!(),
                        };
                        body.instr(instr);
                    }
                    #[cfg(not(feature = "isa_2nd"))]
                    CondBrKind::IfBin(..) => unreachable!(),
                    CondBrKind::IfBinF(cond, rs1, rs2) => {
                        let rs1 = rs1.inner();
                        let rs2 = rs2.inner();
                        let else_ = Offset::Label(else_);
                        let instr = match cond {
                            IfBinFKind::Flt => pseudo_f!(Fbge rs1, rs2, #else_),
                            IfBinFKind::Fge => pseudo_f!(Fblt rs1, rs2, #else_),
                        };
                        body.instr(instr);
                    }
                    CondBrKind::IfUn(cond, rs1) => {
                        let else_ = Offset::Label(else_);
                        let instr = match cond {
                            IfUnIKind::Eqz => pseudo_i!(Bnez rs1, #else_),
                            IfUnIKind::Nez => pseudo_i!(Beqz rs1, #else_),
                            IfUnIKind::Lez => pseudo_i!(Bgtz rs1, #else_),
                            IfUnIKind::Gtz => pseudo_i!(Blez rs1, #else_),
                            IfUnIKind::Gez => pseudo_i!(Bltz rs1, #else_),
                            IfUnIKind::Ltz => pseudo_i!(Bgez rs1, #else_),
                        };
                        body.instr(instr);
                    }
                    CondBrKind::IfUnF(cond, rs1) => {
                        let rs1 = rs1.inner();
                        let else_ = Offset::Label(else_);
                        let instr = match cond {
                            IfUnFKind::Fgtz => pseudo_f!(Fblez rs1, #else_),
                            IfUnFKind::Fltz => pseudo_f!(Fbgez rs1, #else_),
                            IfUnFKind::Feqz => pseudo_f!(Fbnez rs1, #else_),
                            IfUnFKind::Fnez => pseudo_f!(Fbeqz rs1, #else_),
                            IfUnFKind::Flez => pseudo_f!(Fbgtz rs1, #else_),
                            IfUnFKind::Fgez => pseudo_f!(Fbltz rs1, #else_),
                        };
                        body.instr(instr);
                    }
                };
                if !matches!(deque.front(), Some(front) if front.id == then_) {
                    let then_ = Offset::Label(then_);
                    body.instr(pseudo_i!(J #then_));
                }
            }
            Terminator::TailCall(l, args, fargs) => {
                before_call_fn(&mut body, args, fargs);
                call_fn_no_return(&mut body, l);
            }
        }
    }
    body
}

#[derive(Default)]
struct FillRAMap {
    mapping_i: HashMap<IdentSymbol, RegId>,
    mapping_f: HashMap<IdentSymbol, FRegId>,
    prom_map_i: HashMap<FillRAInit, RegId>,
    prom_map_f: HashMap<FillRAInit, FRegId>,
}

struct FillRAInits {
    init_i: Vec<(RegId, FillRAInit)>,
    init_f: Vec<(FRegId, FillRAInit)>,
}

fn fill_ra(i: FillRA<RegId>, f: FillRA<FRegId>) -> (FillRAMap, FillRAInits) {
    (
        FillRAMap {
            mapping_i: i.reg_map,
            mapping_f: f.reg_map,
            prom_map_i: i.prom_map,
            prom_map_f: f.prom_map,
        },
        FillRAInits {
            init_i: i.init,
            init_f: f.init,
        },
    )
}

impl FillRAInits {
    fn into_init_stmts<'a>(
        self,
        globals_map: &mut GlobalVarMap<Ident<'a>>,
    ) -> Vec<Stmt<Label<'a>, RegId, FRegId>> {
        let mut stale_labels = HashSet::new();
        let mut ret = Vec::new();
        for (r, ini) in self.init_i {
            match ini {
                FillRAInit::LoadInt(c) => {
                    if c != 0 {
                        ret.push(Stmt::Assign(Some(I(r)), None, Expr::LoadInt(c)));
                    }
                }
                FillRAInit::LoadF32(_) => unreachable!(),
                FillRAInit::LoadFromLabelDisp(l, disp) => {
                    stale_labels.insert(l);
                    let gv = globals_map.get(&l).expect("target is global");
                    let arr = gv.value.as_array().unwrap();
                    match arr.get(&disp) {
                        CompileTimeConst::AddressOf(l) => {
                            ret.push(Stmt::Assign(
                                Some(I(r)),
                                None,
                                Expr::LoadLabelAddr(Label::Ident(l.to_owned())),
                            ));
                        }
                        CompileTimeConst::Int(c) => {
                            if *c != 0 {
                                ret.push(Stmt::Assign(Some(I(r)), None, Expr::LoadInt(*c)));
                            }
                        }
                        CompileTimeConst::Float(_) => unreachable!(),
                    }
                }
            }
        }

        for (r, ini) in self.init_f {
            match ini {
                FillRAInit::LoadInt(_) => unreachable!(),
                FillRAInit::LoadF32(f) => {
                    if f != 0.0 {
                        ret.push(Stmt::Assign(Some(F(r)), None, Expr::LoadF32(f)));
                    }
                }
                FillRAInit::LoadFromLabelDisp(l, disp) => {
                    stale_labels.insert(l);
                    let gv = globals_map.get(&l).expect("target is global");
                    let arr = gv.value.as_array().unwrap();
                    match arr.get(&disp) {
                        CompileTimeConst::AddressOf(_) | CompileTimeConst::Int(_) => unreachable!(),
                        CompileTimeConst::Float(f) => {
                            if *f != 0.0 {
                                ret.push(Stmt::Assign(Some(F(r)), None, Expr::LoadF32(*f)));
                            }
                        }
                    }
                }
            }
        }
        for l in stale_labels {
            globals_map.remove(&l);
        }
        ret
    }
}

/// exploit register not allocated yet.
struct FillRA<RegId: Register> {
    reg_map: HashMap<IdentSymbol, RegId>,
    prom_map: HashMap<FillRAInit, RegId>,
    init: Vec<(RegId, FillRAInit)>,
}

impl<RegId: Register + std::fmt::Debug> FillRA<RegId> {
    fn new(vacant: Vec<&RegId>, prom: BTreeMap<PromotableGlobal, PromotedIdent>) -> Self {
        let mut index = 0;
        let mut reg_map = HashMap::new();
        let mut prom_map = HashMap::new();
        let mut init = Vec::new();
        for (PromotableGlobal { from, .. }, PromotedIdent { map, .. }) in prom {
            let consume_count = map.len();
            if vacant[index..].len() < consume_count {
                continue;
            }
            for (&&reg, (access, idents)) in vacant[index..(index + consume_count)].iter().zip(map)
            {
                reg_map.extend(idents.into_iter().map(|ident| (ident, reg)));
                let f = FillRAInit::from_promote(&from, access);
                init.push((reg, f.clone()));
                prom_map.insert(f, reg);
            }
            index += consume_count;
        }
        Self {
            reg_map,
            prom_map,
            init,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum FillRAInit {
    LoadInt(i32),
    LoadF32(NotNan<f32>),
    LoadFromLabelDisp(IdentSymbol, i32),
}

impl FillRAInit {
    fn from_promote(from: &PromoteFrom<IdentSymbol>, access: Option<i32>) -> Self {
        match *from {
            PromoteFrom::Label(l) => FillRAInit::LoadFromLabelDisp(l, access.unwrap()),
            PromoteFrom::ConstInt(c) => FillRAInit::LoadInt(c),
            PromoteFrom::ConstF32(c) => FillRAInit::LoadF32(c),
        }
    }
}

pub fn asm_transform(prog: VirtualAsm, c: CollectUsage) -> Prog<Ident, Label, TextSegment<Label>> {
    let (prom_bti, prom_btf) = find_register_promotable(&prog, &c);
    let VirtualAsm {
        float_map,
        mut globals_map,
        fundefs,
        entry_point,
    } = prog;
    let ras: Vec<_> = fundefs
        .iter()
        .map(|f| {
            let la = liveness_analysis(f);
            log::debug!("result of liveness analysis on fn {}:\n{la}", f.name);
            let ra = regalloc(la);
            log::debug!("result of regalloc on fn {}:\n{ra}", f.name);
            ra
        })
        .collect();
    let max_i_arg_len = fundefs.iter().map(|f| f.args.len()).max().unwrap();
    let max_f_arg_len = fundefs.iter().map(|f| f.fargs.len()).max().unwrap();
    let valid_arg_ireg_range = RegId::arg_nth(0)..=RegId::arg_nth(max_i_arg_len - 1);
    let valid_arg_freg_range = FRegId::arg_nth(0)..=FRegId::arg_nth(max_f_arg_len - 1);
    let iregs_vacant: Vec<_> = iregs()
        .par_iter()
        .filter(|r| {
            ras.par_iter()
                .all(|ra| ra.live_range_unions_i[r].live_range_ids.is_empty())
                && !valid_arg_ireg_range.contains(r)
        })
        .collect();
    let fregs_vacant: Vec<_> = fregs()
        .par_iter()
        .filter(|r| {
            ras.par_iter()
                .all(|ra| ra.live_range_unions_f[r].live_range_ids.is_empty())
                && !valid_arg_freg_range.contains(r)
        })
        .collect();
    let (ra2, ra2_init) = fill_ra(
        FillRA::new(iregs_vacant, prom_bti),
        FillRA::new(fregs_vacant, prom_btf),
    );
    let mut ra2_init = Some(ra2_init);
    let fundefs: Vec<_> = fundefs
        .iter()
        .zip(ras)
        .map(|(f, ra)| {
            let mut p = replace_vregs(f, ra, &ra2);
            if f.name == entry_point {
                let before = ra2_init.take().unwrap().into_init_stmts(&mut globals_map);
                for s in before {
                    p.body.front_mut().unwrap().instrs.push_front(s);
                }
            }
            into_instr(p, &float_map)
        })
        .collect();
    Prog {
        float_map,
        globals_map,
        fundefs,
        entry_point,
    }
}
