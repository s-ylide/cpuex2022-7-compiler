use crate::liveness::{InstrPoint, LAResult, ProgramPoint};
use crate::{FRegId, Range, RegId};
use bitvec::prelude::BitArray;
use bitvec::BitArr;
use ir_asm_ast_isa1st::abi::{self, fregs, iregs, Register};
use multimap::MultiMap;
use std::fmt::Display;
use std::{
    collections::{BTreeSet, BinaryHeap, HashMap},
    hash::Hash,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, Mutex,
    },
};
use typedefs::{Ident, Label};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub(crate) struct LiveRangeId(usize);

impl LiveRangeId {
    fn new() -> Self {
        static LIVE_RANGE_ID_GEN: AtomicUsize = AtomicUsize::new(0);
        Self(LIVE_RANGE_ID_GEN.fetch_add(1, Ordering::SeqCst))
    }
}

pub(crate) struct RAResult<'a, 'fun, Label> {
    pub must_save_vars: Vec<&'fun Ident<'a>>,
    pub live_range_unions_i: HashMap<&'static RegId, LiveRangeUnion>,
    pub live_range_unions_f: HashMap<&'static FRegId, LiveRangeUnion>,
    pub live_ranges_i: HashMap<LiveRangeId, LiveRange<&'fun Ident<'a>>>,
    pub live_ranges_f: HashMap<LiveRangeId, LiveRange<&'fun Ident<'a>>>,
    pub restore_right_after: MultiMap<ProgramPoint, (&'fun Ident<'a>, abi::RegKind)>,
    pub bb_param_index: HashMap<&'fun Label, ProgramPoint>,
}

impl<'a, 'fun, Label> Display for RAResult<'a, 'fun, Label> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "must_save_vars:")?;
        writeln!(
            f,
            "\t{}",
            self.must_save_vars
                .iter()
                .map(|v| format!("{v}"))
                .collect::<Vec<_>>()
                .join(", ")
        )?;
        writeln!(f, "restore_after_call:")?;
        let mut v: Vec<_> = self.restore_right_after.iter_all().collect();
        v.sort_by_key(|(p, _)| *p);
        for (point, v) in v {
            writeln!(
                f,
                "\t{point:10}: {}",
                v.iter()
                    .map(|(ident, _)| format!("{ident}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?;
        }
        Ok(())
    }
}

#[derive(PartialEq, Eq)]
pub(crate) struct LiveRange<LiveRangeVar> {
    pub var: LiveRangeVar,
    pub range: Range,
    /// whether this range contains def
    pub is_def_range: bool,
}

impl<LiveRangeVar> LiveRange<LiveRangeVar> {
    fn def_range(var: LiveRangeVar, range: Range) -> Self {
        Self {
            var,
            range,
            is_def_range: true,
        }
    }
    fn use_range(var: LiveRangeVar, range: Range) -> Self {
        Self {
            var,
            range,
            is_def_range: false,
        }
    }
    fn spill_cost_rev(&self, uses: &Range) -> Cost {
        let inter = self.range.clone() & uses;
        let len = self.range.count_ones();
        if len <= 1 {
            Cost(0.0)
        } else {
            Cost(len as f64 / inter.count_ones() as f64)
        }
    }
    fn starts(&self) -> usize {
        self.range.leading_zeros()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct LiveRangeCost {
    pub cost: Cost,
    starts: usize,
    pub live_range_id: LiveRangeId,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub(crate) struct Cost(f64);

impl Eq for Cost {}

impl Ord for Cost {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl PartialOrd for Cost {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct LiveRangeUnion {
    pub live_range_ids: BTreeSet<LiveRangeCost>,
    /// cache
    pub range: Range,
}

impl LiveRangeUnion {
    fn new(program_len: usize) -> Self {
        Self {
            live_range_ids: BTreeSet::new(),
            range: Range::repeat(false, program_len << 1),
        }
    }
    fn zero_range(&mut self, program_len: usize) {
        self.range = Range::repeat(false, program_len << 1);
    }
    fn recalculate_range(&mut self, live_ranges: &LiveRanges, program_len: usize) {
        self.zero_range(program_len);
        for LiveRangeCost { live_range_id, .. } in self.live_range_ids.iter() {
            self.range |= &live_ranges[live_range_id].range;
        }
    }
}

type RestoreAfterCall<'a, 'fun> =
    HashMap<LiveRangeId, Vec<(ProgramPoint, (&'fun Ident<'a>, abi::RegKind))>>;

pub(crate) fn regalloc<'a, 'fun>(
    LAResult {
        defs,
        tys,
        uses,
        calls,
        abi_prefers,
        program_len,
        bb_param_var: bb_param_index,
        live_map,
        ..
    }: LAResult<&'fun Ident<'a>, &'fun Label<'a>>,
) -> RAResult<'a, 'fun, Label<'a>> {
    use rayon::prelude::*;
    let must_save_vars = Arc::new(Mutex::new(Some(Vec::new())));
    let restore_right_after: Arc<Mutex<Option<RestoreAfterCall>>> =
        Arc::new(Mutex::new(Some(HashMap::new())));
    let uses_range: HashMap<_, _> = uses
        .iter_all()
        .map(|(var, v)| (*var, into_range(v.iter(), InstrPoint::Early, program_len)))
        .collect();
    let ((heap_i, mut live_ranges_i), (heap_f, mut live_ranges_f)): (
        (BinaryHeap<_>, HashMap<_, _>),
        _,
    ) = live_map
        .into_par_iter()
        .flat_map(|(var, interval)| {
            let ty = &tys[var];
            let uses = uses_range.get(var).unwrap();
            let interferes: Vec<_> = calls
                .iter()
                .map(|(c, _)| c)
                .filter(|call| interval[call.early()] && interval[call.late()])
                .cloned()
                .collect();
            if !interferes.is_empty() {
                {
                    must_save_vars.lock().unwrap().as_mut().unwrap().push(var);
                }
                log::debug!(
                    "found {var} lives across call on {}.",
                    interferes
                        .iter()
                        .map(|p| format!("#{p}"))
                        .collect::<Vec<_>>()
                        .join(",")
                );
            }
            {
                let live_range_id = LiveRangeId::new();
                if !interferes.is_empty() {
                    {
                        restore_right_after
                            .lock()
                            .unwrap()
                            .as_mut()
                            .unwrap()
                            .insert(
                                live_range_id,
                                interferes
                                    .iter()
                                    .map(|interfere| (*interfere, (var, ty.clone())))
                                    .collect::<Vec<_>>(),
                            );
                    }
                }
                let r = LiveRange::def_range(var, interval);
                vec![(
                    ty,
                    (
                        LiveRangeCost {
                            live_range_id,
                            cost: r.spill_cost_rev(uses),
                            starts: r.starts(),
                        },
                        (live_range_id, r),
                    ),
                )]
            }
        })
        .partition_map(|(ty, v)| match ty {
            abi::RegKind::Int => rayon::iter::Either::Left(v),
            abi::RegKind::Float => rayon::iter::Either::Right(v),
        });
    let mut must_save_vars = must_save_vars.lock().unwrap().take().unwrap();
    let mut restore_right_after: RestoreAfterCall =
        restore_right_after.lock().unwrap().take().unwrap();

    // calculate live ranges
    let mut live_range_unions_i: HashMap<_, _> = iregs()
        .iter()
        .map(|r| (r, LiveRangeUnion::new(program_len)))
        .collect();
    calculate_live_ranges(
        heap_i,
        &mut live_ranges_i,
        abi_prefers.i,
        iregs,
        &mut live_range_unions_i,
        &mut must_save_vars,
        &mut restore_right_after,
        program_len,
        &defs,
        &uses,
    );
    let mut live_range_unions_f: HashMap<_, _> = fregs()
        .iter()
        .map(|r| (r, LiveRangeUnion::new(program_len)))
        .collect();
    calculate_live_ranges(
        heap_f,
        &mut live_ranges_f,
        abi_prefers.f,
        fregs,
        &mut live_range_unions_f,
        &mut must_save_vars,
        &mut restore_right_after,
        program_len,
        &defs,
        &uses,
    );
    let restore_right_after: MultiMap<_, _> = restore_right_after
        .into_values()
        .flat_map(|a| a.into_iter())
        .collect();

    RAResult {
        must_save_vars,
        live_range_unions_i,
        live_range_unions_f,
        live_ranges_i,
        live_ranges_f,
        restore_right_after,
        bb_param_index,
    }
}

type LiveRanges<'fun, 'a> = HashMap<LiveRangeId, LiveRange<&'fun Ident<'a>>>;

#[inline]
#[allow(clippy::too_many_arguments)]
fn calculate_live_ranges<'fun, 'a, RegId: Register>(
    mut heap: BinaryHeap<LiveRangeCost>,
    live_ranges: &mut LiveRanges<'fun, 'a>,
    abi_prefers: HashMap<&'fun Ident<'a>, RegId>,
    candidates_fn: impl Fn() -> &'static Vec<RegId>,
    live_range_unions: &mut HashMap<&RegId, LiveRangeUnion>,
    must_save_vars: &mut Vec<&'fun Ident<'a>>,
    restore_right_after: &mut RestoreAfterCall<'a, 'fun>,
    program_len: usize,
    defs: &HashMap<&'fun Ident, ProgramPoint>,
    uses: &MultiMap<&'fun Ident, ProgramPoint>,
) {
    'pq: while let Some(LiveRangeCost {
        live_range_id,
        cost,
        ..
    }) = heap.pop()
    {
        let LiveRange { var, range, .. } = live_ranges.get(&live_range_id).unwrap();
        // register targeting
        let abi_prefer = abi_prefers.get(var);

        for level in 0..=1 {
            let mut checked_regs: BitArr!(for 64) = BitArray::ZERO;
            for candidate in abi_prefer.iter().cloned().chain(candidates_fn().iter()) {
                let reg_num = candidate.inner() as usize;
                if checked_regs[reg_num] {
                    continue;
                }
                checked_regs.set(reg_num, true);
                let r_union = live_range_unions.get_mut(candidate).unwrap();
                let intersection = r_union.range.clone() & range;
                if level == 0 && intersection.any() {
                    // search for another register
                    continue;
                }
                if level == 1 {
                    if r_union.live_range_ids.last().unwrap().cost <= cost {
                        log::debug!("cannot evict existing ranges");
                        // search for another register
                        continue;
                    }
                    let evicted = r_union.live_range_ids.extract_if(
                        |LiveRangeCost {
                             live_range_id,
                             cost: cost_,
                             ..
                         }| {
                            cost_ > &cost && {
                                let LiveRange { range, .. } =
                                    live_ranges.get(live_range_id).unwrap();
                                (intersection.clone() & range).any()
                            }
                        },
                    );
                    heap.extend(evicted);
                    r_union.recalculate_range(live_ranges, program_len);
                    // fallthrough
                }
                r_union.live_range_ids.insert(LiveRangeCost {
                    live_range_id,
                    cost,
                    starts: range.leading_zeros(),
                });
                r_union.range |= range;
                continue 'pq;
            }
        }
        log::debug!("no room for `{var}`, splitting it into several ranges");
        let splitted_use_ranges = {
            // after this step, no need to restore *right* after the call
            // (actually value need to be restored before used)
            restore_right_after.remove(&live_range_id);
            let LiveRange { var, range, .. } = live_ranges.get_mut(&live_range_id).unwrap();
            must_save_vars.push(var);
            *range = Range::repeat(false, 2 * program_len);
            let def: ProgramPoint = defs[var];
            range.set(def.late(), true);
            let uses = uses.get_vec(var).unwrap();
            let splitted_use_ranges: Vec<_> = uses
                .iter()
                .map(|u| {
                    let live_range_id = LiveRangeId::new();
                    let mut range = Range::repeat(false, 2 * program_len);
                    range.set(u.early(), true);
                    (live_range_id, LiveRange::<&Ident>::use_range(var, range))
                })
                .collect();
            // retry this range
            heap.push(LiveRangeCost {
                live_range_id,
                cost: Cost(0.0),
                starts: def.late(),
            });
            // also push splitted ranges
            heap.extend(
                splitted_use_ranges
                    .iter()
                    .map(|(live_range_id, r)| LiveRangeCost {
                        live_range_id: *live_range_id,
                        cost: Cost(0.0),
                        starts: r.starts(),
                    }),
            );
            splitted_use_ranges
        };
        live_ranges.extend(splitted_use_ranges);
    }
}

fn into_range<'a>(
    it: impl Iterator<Item = &'a ProgramPoint>,
    io: InstrPoint,
    program_len: usize,
) -> Range {
    let mut bv = Range::repeat(false, 2 * program_len);
    for index in it {
        bv.set(index.get_index(io), true);
    }
    bv
}
