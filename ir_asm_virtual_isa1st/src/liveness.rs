use bitvec::prelude::*;
use ir_asm_ast_isa1st::abi::{FRegId, RegId, RegKind, Register, REG_A0, REG_FA0};
use ir_asm_virtual_ast_isa1st::{
    Branch, CondBr, CondBrKind, Expr, FVReg, FunDef, IVReg, IntoInner, LetBound, Stmt, SymbOrImm,
    Terminator,
};
use multimap::MultiMap;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Display,
    hash::Hash,
};
use typedefs::{Ident, Label};

use crate::{Range, RangeView};

pub(crate) struct LAResult<Var, Label> {
    pub tys: HashMap<Var, RegKind>,
    pub defs: HashMap<Var, ProgramPoint>,
    pub uses: MultiMap<Var, ProgramPoint>,
    pub path: MultiMap<ProgramPoint, ProgramPoint>,
    pub calls: Vec<(ProgramPoint, Label)>,
    pub abi_prefers: AbiPrefs<Var>,
    pub program_len: usize,
    pub bb_param_var: HashMap<Label, ProgramPoint>,
    pub live_map: Vec<(Var, Range)>,
}

impl<Var: Display + Eq + Hash, Label: Display> Display for LAResult<Var, Label> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.program_len > 1000 {
            writeln!(
                f,
                "program_len == {} too long. omitted range view.",
                self.program_len
            )?;
        } else {
            let view = RangeView::new(self.live_map.iter(), self.program_len);
            writeln!(f, "{view}")?;
        }

        writeln!(f, "defs:")?;
        let mut v: Vec<_> = self.defs.iter().collect();
        v.sort_by_key(|(_, p)| *p);
        for (v, point) in v {
            writeln!(f, "\t{v}: {point:10}")?;
        }
        writeln!(f, "uses:")?;
        let mut v: Vec<_> = self.uses.iter_all().collect();
        v.sort_by_key(|(_, p)| p.first().unwrap());
        for (v, points) in v {
            writeln!(
                f,
                "\t{v}: {}",
                points
                    .iter()
                    .map(|point| format!("{point:10}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        writeln!(f, "edges:")?;
        let mut v: Vec<_> = self.path.iter_all().collect();
        v.sort_by_key(|(n, _)| *n);
        for (n, ms) in v {
            let next = n.next();
            for m in ms {
                if &next != m {
                    writeln!(f, "\t{n:10} -> {m:10}")?;
                }
            }
        }
        writeln!(f, "abi_preferences:")?;
        for (v, id) in self.abi_prefers.i.iter() {
            writeln!(f, "\t{v}: {id}")?;
        }
        for (v, id) in self.abi_prefers.f.iter() {
            writeln!(f, "\t{v}: {id}")?;
        }
        writeln!(f, "bb_param_var:")?;
        let mut v: Vec<_> = self.bb_param_var.iter().collect();
        v.sort_by_key(|(_, p)| *p);
        for (n, p) in v {
            writeln!(f, "\t{n}: {p}")?;
        }
        Ok(())
    }
}

pub(crate) struct AbiPrefs<Var> {
    pub i: HashMap<Var, RegId>,
    pub f: HashMap<Var, FRegId>,
}

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub(crate) enum InstrPoint {
    Early,
    Late,
}

impl InstrPoint {
    #[inline]
    pub fn inner(self) -> usize {
        match self {
            InstrPoint::Early => 0,
            InstrPoint::Late => 1,
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ProgramPoint(usize);

impl Display for ProgramPoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl ProgramPoint {
    pub fn new() -> Self {
        Self(0)
    }
    pub fn from(i: usize) -> Self {
        Self(i)
    }
    pub fn incr(&mut self) {
        self.0 += 1;
    }
    pub fn next(&self) -> Self {
        let mut copy = *self;
        copy.incr();
        copy
    }
    pub fn inner(&self) -> usize {
        self.0
    }
    pub fn get_index(&self, io: InstrPoint) -> usize {
        2 * self.0 + io.inner()
    }
    pub fn early(&self) -> usize {
        self.get_index(InstrPoint::Early)
    }
    pub fn late(&self) -> usize {
        self.get_index(InstrPoint::Late)
    }
}

pub(crate) fn liveness_analysis<'a, 'fun>(
    f: &'fun FunDef<Label<'a>, IVReg<'a>, FVReg<'a>>,
) -> LAResult<&'fun Ident<'a>, &'fun Label<'a>> {
    let mut vars = HashSet::new();
    let mut tys = HashMap::new();
    let mut uses = MultiMap::new();
    let mut defs = HashMap::new();
    let mut bb_param_var = HashMap::new();
    let mut program_point = ProgramPoint::new();
    let mut calls = Vec::new();
    let mut abi_prefers = AbiPrefs {
        i: HashMap::new(),
        f: HashMap::new(),
    };
    let mut edges = MultiMap::new();
    let mut edges_rev = MultiMap::new();
    macro_rules! add_edge {
        ($n:ident, $m:ident) => {
            edges.insert($n, $m);
            edges_rev.insert($m, $n);
        };
    }
    macro_rules! def_var {
        ($e:expr, $t:expr) => {
            let v = $e;
            assert!(!defs.contains_key(&v), "{v}");
            defs.insert(v, program_point);
            tys.insert(v, $t);
            vars.insert(v);
        };
    }
    macro_rules! use_var {
        ($e:expr) => {
            let v = $e;
            uses.insert(v, program_point);
            // vars.insert(v);
        };
    }
    let mut bb_index_range = HashMap::new();
    for (n, (arg, _)) in f.args.iter().enumerate() {
        let arg = arg.inner_ref();
        def_var!(arg, RegKind::Int);
        abi_prefers.i.insert(arg, RegId::arg_nth(n));
    }
    for (n, (arg, _)) in f.fargs.iter().enumerate() {
        let arg = arg.inner_ref();
        def_var!(arg, RegKind::Float);
        abi_prefers.f.insert(arg, FRegId::arg_nth(n));
    }
    let arg_pp = program_point;
    for bb in &f.body {
        let mut n = None;
        let bb_begin_index = match &bb.block_param {
            v if v.is_empty() => program_point.next(),
            v => {
                program_point.incr();
                bb_param_var.insert(&bb.id, program_point);
                for LetBound { name, ty: _ } in v {
                    let t = name.ty();
                    def_var!(name.inner_ref(), t);
                }
                n = Some(program_point);
                program_point
            }
        };
        for instr in &bb.instrs {
            program_point.incr();
            let m = program_point;
            if let Some(n) = n.take() {
                add_edge!(n, m);
            }
            match instr {
                Stmt::IncrABI(_, _) => (),
                Stmt::Assign(d, _, u) => {
                    if let Some(d) = d {
                        def_var!(d.inner_ref(), d.ty());
                    }
                    match u {
                        Expr::Load(i, _) | Expr::Mov(i) | Expr::LoadFromLabelDisp(Some(i), ..) => {
                            if let Some(i) = i.as_v() {
                                use_var!(i.inner_ref());
                            }
                        }
                        Expr::IUnOp(_, i) => {
                            use_var!(i.inner_ref());
                        }
                        Expr::MovF(f) => {
                            if let Some(f) = f.as_v() {
                                use_var!(f.inner_ref());
                            }
                        }
                        Expr::FUnOp(_, f) => {
                            if let Some(f) = f.as_v() {
                                use_var!(f.inner_ref());
                            }
                        }
                        Expr::BBinOp(_, i1, i2) => {
                            use_var!(i1.inner_ref());
                            use_var!(i2.inner_ref());
                        }
                        Expr::IBinOp(_, i1, i2) => {
                            use_var!(i1.inner_ref());
                            if let SymbOrImm::Sym(i2) = i2 {
                                use_var!(i2.inner_ref());
                            }
                        }
                        Expr::FBinOp(_, f1, f2) => {
                            if let Some(f) = f1.as_v() {
                                use_var!(f);
                            }
                            if let Some(f) = f2.as_v() {
                                use_var!(f);
                            }
                        }
                        Expr::FTerOp(_, f1, f2, f3) => {
                            if let Some(f) = f1.as_v() {
                                use_var!(f);
                            }
                            if let Some(f) = f2.as_v() {
                                use_var!(f);
                            }
                            if let Some(f) = f3.as_v() {
                                use_var!(f);
                            }
                        }
                        Expr::CallDirectly(l, is, fs) => {
                            calls.push((program_point, l));
                            for (n, i) in is.iter().enumerate() {
                                let i = i.inner_ref();
                                use_var!(i);
                                abi_prefers.i.insert(i, RegId::arg_nth(n));
                            }
                            for (n, f) in fs.iter().enumerate() {
                                let f = f.inner_ref();
                                use_var!(f);
                                abi_prefers.f.insert(f, FRegId::arg_nth(n));
                            }
                        }
                        Expr::Intrinsic(_, is, fs) => {
                            for (n, i) in is.iter().enumerate() {
                                let i = i.inner_ref();
                                use_var!(i);
                                abi_prefers.i.insert(i, RegId::arg_nth(n));
                            }
                            for (n, f) in fs.iter().enumerate() {
                                let f = f.inner_ref();
                                use_var!(f);
                                abi_prefers.f.insert(f, FRegId::arg_nth(n));
                            }
                        }
                        Expr::Nop
                        | Expr::LoadInt(_)
                        | Expr::LoadF32(_)
                        | Expr::LoadLabelAddr(_)
                        | Expr::LoadFromLabelDisp(None, ..) => (),
                    }
                }
                Stmt::Store(pv1, pv2, _) => {
                    if let Some(u) = pv1.as_v() {
                        use_var!(u.inner_ref());
                    }
                    if let Some(u) = pv2.as_v() {
                        use_var!(u.inner_ref());
                    }
                }
                Stmt::StoreF(pv1, pv2, _) => {
                    if let Some(u) = pv1.as_v() {
                        use_var!(u.inner_ref());
                    }
                    if let Some(u) = pv2.as_v() {
                        use_var!(u.inner_ref());
                    }
                }
                Stmt::StoreLabelDisp(i, i1, _, _) => {
                    if let Some(i) = i1.as_ref().and_then(|i| i.as_v()) {
                        use_var!(i.inner_ref());
                    }
                    if let Some(i) = i.as_v() {
                        use_var!(i.inner_ref());
                    }
                }
                Stmt::StoreFLabelDisp(f, i1, _, _) => {
                    if let Some(i) = i1.as_ref().and_then(|i| i.as_v()) {
                        use_var!(i.inner_ref());
                    }
                    if let Some(f) = f.as_v() {
                        use_var!(f.inner_ref());
                    }
                }
            }
            n = Some(program_point);
        }
        {
            let n = program_point;
            program_point.incr();
            let m = program_point;
            bb_index_range.insert(&bb.id, (bb_begin_index, program_point));
            // connect last instr and terminator
            add_edge!(n, m);
            match &bb.terminator {
                Terminator::Exit | Terminator::End => (),
                Terminator::Ret(u) => {
                    let u = u.inner_ref();
                    use_var!(u);
                    match f.ret {
                        ty::ConcTy::Float => {
                            abi_prefers.f.insert(u, REG_FA0);
                        }
                        _ => {
                            abi_prefers.i.insert(u, REG_A0);
                        }
                    }
                }
                Terminator::Branch(Branch(_, u)) => {
                    for a in u {
                        use_var!(a.rhs().inner_ref());
                    }
                }
                Terminator::CondBr(CondBr(c, ..)) => match c {
                    CondBrKind::IfBin(_, u1, u2, ..) => {
                        use_var!(u1.inner_ref());
                        if let Some(u2) = u2.as_ident() {
                            use_var!(u2);
                        }
                    }
                    CondBrKind::IfBinF(_, u1, u2, ..) => {
                        if let Some(f) = u1.as_v() {
                            use_var!(f);
                        }
                        if let Some(f) = u2.as_v() {
                            use_var!(f);
                        }
                    }
                    CondBrKind::IfUn(_, u, ..) => {
                        use_var!(u.inner_ref());
                    }
                    CondBrKind::IfUnF(_, u, ..) => {
                        if let Some(f) = u.as_v() {
                            use_var!(f);
                        }
                    }
                },
                Terminator::TailCall(_, is, fs) => {
                    for (n, i) in is.iter().enumerate() {
                        let i = i.inner_ref();
                        use_var!(i);
                        abi_prefers.i.insert(i, RegId::arg_nth(n));
                    }
                    for (n, f) in fs.iter().enumerate() {
                        let f = f.inner_ref();
                        use_var!(f);
                        abi_prefers.f.insert(f, FRegId::arg_nth(n));
                    }
                }
            }
        }
    }
    if let Some(ent_bb) = f.body.front() {
        let bb_begin_index = bb_index_range[&ent_bb.id].0;
        add_edge!(arg_pp, bb_begin_index);
    }
    for bb in &f.body {
        let u = &bb.id;
        let bb_end_index = bb_index_range[u].1;
        use Terminator::*;
        match &bb.terminator {
            Ret(_) | Exit | End | TailCall(..) => (),
            Branch(self::Branch(l, _)) => {
                let bb_begin_index = bb_index_range[l].0;
                add_edge!(bb_end_index, bb_begin_index);
            }
            CondBr(self::CondBr(_, l1, l2)) => {
                let bb_begin_index = bb_index_range[l1].0;
                add_edge!(bb_end_index, bb_begin_index);
                let bb_begin_index = bb_index_range[l2].0;
                add_edge!(bb_end_index, bb_begin_index);
            }
        };
    }
    use rayon::prelude::*;

    let program_len = program_point.inner() + 1;
    let live_map = vars.into_par_iter().flat_map(|a| {
        let def = defs[a];
        let uses = uses.get_vec(a);
        uses?;
        let uses: HashSet<_> = uses.unwrap().iter().collect();
        let count = 2 * program_len;
        let mut work_set: VecDeque<_> = (0..program_len)
            .flat_map(|n| {
                use InstrPoint::*;
                let n = ProgramPoint::from(n);
                [(Early, n), (Late, n)]
            })
            .collect();
        let mut lives = BitVec::repeat(false, count);
        macro_rules! get_val {
            ($t:tt $n:expr) => {
                lives[$n.get_index($t)]
            };
        }
        while let Some((io, n)) = work_set.pop_front() {
            use InstrPoint::*;
            let index = n.get_index(io);
            let x = match io {
                Early => (get_val![Late n] && def != n) || uses.contains(&n),
                Late => {
                    let ms = edges.get_vec(&n);
                    match ms {
                        Some(ms) => ms.iter().any(|m| get_val![Early m]),
                        None => false,
                    }
                }
            };
            if x != lives[index] {
                lives.set(index, x);
                match io {
                    Early => {
                        let m = n;
                        if let Some(deps) = edges_rev.get_vec(&m) {
                            work_set.extend(deps.iter().map(|n| (Late, *n)));
                        }
                    }
                    Late => {
                        work_set.push_back((Early, n));
                    }
                };
            }
        }
        Some((a, lives))
    });
    LAResult {
        live_map: live_map.collect(),
        defs,
        tys,
        uses,
        calls,
        path: edges,
        program_len,
        bb_param_var,
        abi_prefers,
    }
}
