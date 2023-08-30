use ir_knorm::Continue;
use ordered_float::NotNan;
use pervasives::V_ASM_PERVASIVES;
use typedefs::{Ident, IdentSymbol, IfBranch, IfCond, IfExpr, Label};

use ast::{ConstKind, IBinOpKind};
use ir_asm_ast_isa1st::{abi::*, *};
use ir_asm_virtual_ast_isa1st::{
    builder::{assign, discard},
    BasicBlock, BlockParamAssign, BlockParamDef, Branch, CondBr, CondBrKind, Expr, FVReg, FunDef,
    IVReg, IorF, LetBound, LetBoundKind, PhysOrVirt, Prog, Stmt, StmtList, SymbOrImm, Terminator,
    VAsmFunDef, VirtualAsm,
};
use ir_closure::IrNode;
use typedefs::{MaybeConst, VarDef};

use std::{
    borrow::Cow,
    collections::{HashMap, VecDeque},
};
use ty::ConcTy;

use PhysOrVirt::*;

fn float_encoding(f: NotNan<f32>) -> u32 {
    f.to_bits()
}

pub fn float_constant<'a, I, F>(
    f: NotNan<f32>,
    data: &mut FloatConstMap<Label<'a>>,
) -> Expr<Label<'a>, I, F> {
    let re = float_encoding(f);
    let (_, f) = data.entry(re).or_insert_with(|| {
        let l = Label::uniq_name(format!("f32_{f:.8}"));
        (l, f)
    });
    Expr::LoadF32(*f)
}

enum FlatExpr<L, IA, FA> {
    Branches {
        term: Terminator<IA, FA, L>,
        then_: L,
        then_cl: FlatExprs<L, IA, FA>,
        then_br: Option<BlockParamAssign<IA, FA>>,
        else_: L,
        else_cl: FlatExprs<L, IA, FA>,
        else_br: Option<BlockParamAssign<IA, FA>>,
        endif_: L,
        lb: Option<LetBound<IA, FA>>,
        coalesced: bool,
    },
    LoopBranch {
        loop_label: L,
        loop_init_param: Vec<BlockParamAssign<IA, FA>>,
        loop_br: Option<BlockParamAssign<IA, FA>>,
        body: FlatExprs<L, IA, FA>,
        endloop_label: L,
        lb: Option<LetBound<IA, FA>>,
        coalesced: bool,
    },
    Continue {
        br: Terminator<IA, FA, L>,
    },
    Stmts {
        precedes: StmtList<L, IA, FA>,
        bounded: Option<Expr<L, IA, FA>>,
        follows: StmtList<L, IA, FA>,
    },
}

impl<'a> FlatExpr<Label<'a>, IVReg<'a>, FVReg<'a>> {
    /// binds unbounded expr.
    pub fn assign(&mut self, x: Cow<Ident<'a>>, ty: ConcTy, mut coalesce: Option<Label<'a>>) {
        match self {
            FlatExpr::Branches {
                then_cl,
                then_br,
                else_cl,
                else_br,
                coalesced,
                endif_,
                ..
            } => {
                if let Some(e) = &coalesce {
                    *endif_ = e.clone();
                    *coalesced = true;
                } else {
                    coalesce = Some(endif_.clone());
                }
                let then_name = x.updated();
                if let Some(al) = then_br.as_mut() {
                    if let Some(v) = IorF::from_name_ty(Cow::Borrowed(&then_name), &ty) {
                        al.set_rhs(v)
                    }
                }
                then_cl.assign(Cow::Owned(then_name), ty.clone(), coalesce.clone());
                let else_name = x.updated();
                if let Some(bl) = else_br.as_mut() {
                    if let Some(v) = IorF::from_name_ty(Cow::Borrowed(&else_name), &ty) {
                        bl.set_rhs(v)
                    }
                }
                else_cl.assign(Cow::Owned(else_name), ty, coalesce);
            }
            FlatExpr::LoopBranch {
                loop_br,
                body,
                endloop_label,
                coalesced,
                ..
            } => {
                if let Some(e) = &coalesce {
                    *endloop_label = e.clone();
                    *coalesced = true;
                } else {
                    coalesce = Some(endloop_label.clone());
                }
                let break_name = x.updated();
                if let Some(al) = loop_br.as_mut() {
                    if let Some(v) = IorF::from_name_ty(Cow::Borrowed(&break_name), &ty) {
                        al.set_rhs(v)
                    }
                }
                body.assign(Cow::Owned(break_name), ty, coalesce);
            }
            FlatExpr::Continue { .. } => (),
            FlatExpr::Stmts {
                precedes, bounded, ..
            } => {
                if let Some(e) = bounded.take() {
                    precedes.push_back(assign(x, ty, e));
                }
            }
        }
    }
}

impl<L, IA, FA> FlatExpr<L, IA, FA> {
    #[inline]
    pub fn anorm(
        precedes: impl IntoIterator<Item = Stmt<L, IA, FA>>,
        value: Expr<L, IA, FA>,
    ) -> Self {
        Self::Stmts {
            precedes: precedes.into_iter().collect(),
            bounded: Some(value),
            follows: VecDeque::new(),
        }
    }
    #[inline]
    pub fn extra2(
        value: Expr<L, IA, FA>,
        follows: impl IntoIterator<Item = Stmt<L, IA, FA>>,
    ) -> Self {
        Self::Stmts {
            precedes: VecDeque::new(),
            bounded: Some(value),
            follows: follows.into_iter().collect(),
        }
    }
}

struct FlatExprs<L, IA, FA>(VecDeque<FlatExpr<L, IA, FA>>);

impl<'a> FlatExprs<Label<'a>, IVReg<'a>, FVReg<'a>> {
    pub fn assign(&mut self, x: Cow<Ident<'a>>, ty: ConcTy, coalesce: Option<Label<'a>>) {
        self.0.back_mut().unwrap().assign(x, ty, coalesce);
    }
}

impl<L, IA, FA> FlatExprs<L, IA, FA> {
    pub fn tail(tail: FlatExpr<L, IA, FA>) -> Self {
        Self(VecDeque::from_iter([tail]))
    }
    #[inline]
    pub fn seq(lets: impl IntoIterator<Item = Stmt<L, IA, FA>>, mut value: Self) -> Self {
        let head = FlatExpr::Stmts {
            precedes: lets.into_iter().collect(),
            bounded: None,
            follows: StmtList::new(),
        };
        value.0.push_front(head);
        value
    }
    #[inline]
    pub fn concat(mut self, other: Self) -> Self {
        self.0.extend(other.0);
        self
    }
}

impl<'a> FlatExprs<Label<'a>, IVReg<'a>, FVReg<'a>> {
    pub fn into_bb(
        self,
        fn_ret_ty: ConcTy,
    ) -> VecDeque<BasicBlock<Label<'a>, IVReg<'a>, FVReg<'a>>> {
        let mut current_label = Label::name("entry");
        let mut param_def = None;
        let mut instrs = VecDeque::new();
        let mut disable_next = false;
        self.into_bb_inner_last(
            fn_ret_ty,
            &mut current_label,
            &mut param_def,
            &mut instrs,
            &mut disable_next,
        )
    }
    /// insert return or exit.
    fn into_bb_inner_last(
        mut self,
        fn_ret_ty: ConcTy,
        current_label: &mut Label<'a>,
        param_def: &mut Option<BlockParamDef<IVReg<'a>, FVReg<'a>>>,
        instrs: &mut StmtList<Label<'a>, IVReg<'a>, FVReg<'a>>,
        disable_next: &mut bool,
    ) -> VecDeque<BasicBlock<Label<'a>, IVReg<'a>, FVReg<'a>>> {
        let last = self.0.pop_back().unwrap();
        let mut ret = self.into_bb_inner(current_label, param_def, instrs, disable_next);
        macro_rules! param {
            (with $i:ident) => {
                $i.take().unwrap_or_default()
            };
            (()) => {
                BlockParamDef::default()
            };
        }
        macro_rules! yields {
            ($instrs:ident terminates $term:expr, $($tt:tt)*) => {
                if *disable_next {
                    *disable_next = false;
                } else {
                    ret.push_back(BasicBlock {
                        id: current_label.clone(),
                        instrs: std::mem::take($instrs),
                        terminator: $term,
                        block_param: param!($($tt)*),
                    });
                }
            };
        }
        match last {
            FlatExpr::Branches {
                term,
                then_,
                then_cl,
                else_,
                else_cl,
                lb,
                ..
            } => {
                assert!(lb.is_none());
                yields!(instrs terminates term, with param_def);
                *current_label = then_;
                let r = then_cl.into_bb_inner_last(
                    fn_ret_ty.clone(),
                    current_label,
                    param_def,
                    instrs,
                    disable_next,
                );
                ret.extend(r);
                *current_label = else_;
                let r = else_cl.into_bb_inner_last(
                    fn_ret_ty,
                    current_label,
                    param_def,
                    instrs,
                    disable_next,
                );
                ret.extend(r);
            }
            FlatExpr::LoopBranch {
                loop_label,
                loop_init_param,
                body,
                lb,
                ..
            } => {
                assert!(lb.is_none());
                let loop_param = loop_init_param.iter().map(|a| a.param.clone()).collect();
                let term = Terminator::Branch(Branch(loop_label.clone(), loop_init_param));
                yields!(instrs terminates term, with param_def);
                *current_label = loop_label;
                *param_def = Some(loop_param);
                let r = body.into_bb_inner_last(
                    fn_ret_ty,
                    current_label,
                    param_def,
                    instrs,
                    disable_next,
                );
                ret.extend(r);
            }
            FlatExpr::Continue { br } => {
                yields!(instrs terminates br, with param_def);
            }
            FlatExpr::Stmts {
                precedes: exprs,
                bounded: mut o,
                follows: follow,
            } => {
                instrs.extend(exprs);
                let terminator = {
                    let x = Ident::ubiq_name("retval");
                    match abi::RegKind::from_concty(&fn_ret_ty) {
                        Some(c) => {
                            if let Some(e) = o.take() {
                                instrs.push_back(assign(Cow::Borrowed(&x), fn_ret_ty, e));
                            }
                            let ret = match c {
                                abi::RegKind::Int => IorF::I(IVReg(x)),
                                abi::RegKind::Float => IorF::F(FVReg(x)),
                            };
                            Terminator::Ret(ret)
                        }
                        None => {
                            if let Some(e) = o.take() {
                                instrs.push_back(discard(e));
                            }
                            Terminator::Exit
                        }
                    }
                };
                instrs.extend(follow);
                yields!(instrs terminates terminator, with param_def);
            }
        }
        ret
    }
    fn into_bb_inner(
        mut self,
        current_label: &mut Label<'a>,
        param_def: &mut Option<BlockParamDef<IVReg<'a>, FVReg<'a>>>,
        instrs: &mut StmtList<Label<'a>, IVReg<'a>, FVReg<'a>>,
        // disable next bb creation
        disable_next: &mut bool,
    ) -> VecDeque<BasicBlock<Label<'a>, IVReg<'a>, FVReg<'a>>> {
        let mut ret = VecDeque::new();
        macro_rules! param {
            (with $i:ident) => {
                $i.take().unwrap_or_default()
            };
            (()) => {
                BlockParamDef::default()
            };
        }
        macro_rules! yields {
            ($instrs:ident terminates $term:expr, $($tt:tt)*) => {
                if *disable_next {
                    *disable_next = false;
                } else {
                    ret.push_back(BasicBlock {
                        id: current_label.clone(),
                        instrs: std::mem::take($instrs),
                        terminator: $term,
                        block_param: param!($($tt)*),
                    });
                }
            };
        }
        while let Some(flat) = self.0.pop_front() {
            match flat {
                FlatExpr::Branches {
                    term,
                    then_,
                    then_cl,
                    then_br,
                    else_,
                    else_cl,
                    else_br,
                    endif_,
                    lb,
                    coalesced,
                } => {
                    yields!(instrs terminates term, with param_def);
                    *current_label = then_;
                    let r = then_cl.into_bb_inner(current_label, param_def, instrs, disable_next);
                    ret.extend(r);
                    yields!(instrs terminates Terminator::Branch(Branch(endif_.clone(), then_br.into_iter().collect())), with param_def);
                    *current_label = else_;
                    let r = else_cl.into_bb_inner(current_label, param_def, instrs, disable_next);
                    ret.extend(r);
                    yields!(instrs terminates Terminator::Branch(Branch(endif_.clone(), else_br.into_iter().collect())), with param_def);
                    if !coalesced {
                        *current_label = endif_;
                        *param_def = Some(lb.into_iter().collect());
                    }
                    *disable_next = coalesced;
                }
                FlatExpr::LoopBranch {
                    loop_label,
                    loop_init_param,
                    loop_br,
                    body,
                    endloop_label,
                    lb,
                    coalesced,
                } => {
                    let loop_param = loop_init_param.iter().map(|a| a.param.clone()).collect();
                    let term = Terminator::Branch(Branch(loop_label.clone(), loop_init_param));
                    yields!(instrs terminates term, with param_def);
                    *current_label = loop_label;
                    *param_def = Some(loop_param);
                    let r = body.into_bb_inner(current_label, param_def, instrs, disable_next);
                    ret.extend(r);
                    yields!(instrs terminates Terminator::Branch(Branch(endloop_label.clone(), loop_br.into_iter().collect())), with param_def);
                    if !coalesced {
                        *current_label = endloop_label;
                        *param_def = Some(lb.into_iter().collect());
                    }
                    *disable_next = coalesced;
                }
                FlatExpr::Continue { br } => {
                    yields!(instrs terminates br, with param_def);
                    *disable_next = true;
                }
                FlatExpr::Stmts {
                    precedes,
                    bounded,
                    follows,
                } => {
                    if bounded.is_some() {
                        panic!("into_bb: unbound expr found: {:?}", bounded.unwrap())
                    }
                    instrs.extend(precedes);
                    instrs.extend(follows);
                }
            }
        }

        ret
    }
}

fn virtasm_transform_expr<'a>(
    data: &mut FloatConstMap<Label<'a>>,
    globals_map: &mut GlobalVarMap<Ident<'a>>,
    toplevel_var_types: &HashMap<Ident<'a>, ty::Ty>,
    e: IrNode<'a>,
    let_bound: LetBoundKind<IVReg<'a>, FVReg<'a>>,
) -> FlatExprs<Label<'a>, IVReg<'a>, FVReg<'a>> {
    use Expr::*;
    use MaybeConst::*;
    use Stmt::*;
    macro_rules! tail {
        ($e:expr) => {
            FlatExprs::tail(FlatExpr::Stmts {
                precedes: StmtList::new(),
                bounded: Some($e),
                follows: StmtList::new(),
            })
        };
        ($before:expr, $e:expr) => {
            FlatExprs::tail(FlatExpr::Stmts {
                precedes: $before,
                bounded: Some($e),
                follows: StmtList::new(),
            })
        };
    }
    macro_rules! tail_stmt {
        ($e:expr) => {
            FlatExprs::tail(FlatExpr::Stmts {
                precedes: StmtList::from_iter($e),
                bounded: None,
                follows: StmtList::new(),
            })
        };
    }
    match e {
        IrNode::Const(ConstKind::Unit) => tail!(Nop),
        IrNode::Const(ConstKind::Bool(_)) => unreachable!(),
        IrNode::Const(c) => {
            let t = match ConstSource::from_const(c) {
                ConstSource::Int(i) => match i {
                    IConstSource::Value(i) => LoadInt(i),
                    IConstSource::Register(r) => Mov(P(r)),
                },
                ConstSource::Float(f) => match f {
                    FConstSource::Value(f) => float_constant(f, data),
                    FConstSource::MovF(r) => MovF(P(r)),
                    FConstSource::Fneg(r) => FUnOp(ast::FUnOpKind::Fneg, P(r)),
                },
            };
            tail!(t)
        }
        IrNode::IUnOp(k, x) => tail!(IUnOp(k, IVReg(x))),
        IrNode::IBinOp(op, x, Variable(y)) => {
            tail!(IBinOp(op, IVReg(x), SymbOrImm::Sym(IVReg(y))))
        }
        IrNode::IBinOp(op, x, Constant(imm)) => {
            tail!(IBinOp(op, IVReg(x), SymbOrImm::Imm(*imm.as_int().unwrap())))
        }
        IrNode::FUnOp(k, x) => tail!(FUnOp(k, V(FVReg(x)))),
        IrNode::FBinOp(op, x, y) => tail!(FBinOp(op, V(FVReg(x)), V(FVReg(y)))),
        IrNode::FTerOp(op, x, y, z) => tail!(FTerOp(op, V(FVReg(x)), V(FVReg(y)), V(FVReg(z)))),
        IrNode::If(IfExpr { cond, clauses }) => {
            let then_ = Label::name("then");
            let else_ = Label::name("else");
            let condbr = Terminator::CondBr(CondBr(
                match cond {
                    IfCond::Bin {
                        op,
                        lhs: VarDef { name: lhs, ty },
                        rhs,
                    } => match RegKind::from_concty(&ty.as_concty().unwrap()).unwrap() {
                        RegKind::Int => CondBrKind::IfBin(
                            op.try_into_i().unwrap(),
                            IVReg(lhs),
                            SymbOrImm::Sym(IVReg(rhs)),
                        ),
                        RegKind::Float => CondBrKind::IfBinF(
                            op.try_into_f().unwrap(),
                            V(FVReg(lhs)),
                            V(FVReg(rhs)),
                        ),
                    },
                    IfCond::Un {
                        op,
                        lhs: VarDef { name: lhs, ty },
                    } => match RegKind::from_concty(&ty.as_concty().unwrap()).unwrap() {
                        RegKind::Int => CondBrKind::IfUn(op.try_into_i().unwrap(), IVReg(lhs)),
                        RegKind::Float => {
                            CondBrKind::IfUnF(op.try_into_f().unwrap(), V(FVReg(lhs)))
                        }
                    },
                },
                then_.clone(),
                else_.clone(),
            ));
            let endif_ = Label::name("endif");

            match clauses {
                IfBranch::ThenElse {
                    then_: e1,
                    else_: e2,
                } => {
                    let e1 = virtasm_transform_expr(
                        data,
                        globals_map,
                        toplevel_var_types,
                        *e1,
                        let_bound.clone(),
                    );
                    let e2 = virtasm_transform_expr(
                        data,
                        globals_map,
                        toplevel_var_types,
                        *e2,
                        let_bound.clone(),
                    );
                    FlatExprs::tail(FlatExpr::Branches {
                        term: condbr,
                        then_,
                        then_cl: e1,
                        then_br: let_bound.clone().map(BlockParamAssign::new),
                        else_,
                        else_cl: e2,
                        else_br: let_bound.clone().map(BlockParamAssign::new),
                        endif_,
                        lb: let_bound,
                        coalesced: false,
                    })
                }
            }
        }
        IrNode::Let(d, e1, e2) => 'v: {
            let VarDef { name, ty } = d.clone();
            if toplevel_var_types.contains_key(&name) {
                let mut ty = ty.as_concty().unwrap();
                if let ConcTy::Unit | ConcTy::Tuple(..) | ConcTy::Array(..) = &ty {
                    let o = eval_constant_ctxt(globals_map, &e1, &mut ty);
                    if let ConcTy::Unit = ty {
                        break 'v virtasm_transform_expr(
                            data,
                            globals_map,
                            toplevel_var_types,
                            *e2,
                            let_bound,
                        );
                    }
                    if let Some(value) = o {
                        let size = sizeof_concty(&ty).unwrap();
                        globals_map.insert(
                            name.clone(),
                            GlobalVar {
                                name,
                                size,
                                ty,
                                value,
                            },
                        );
                        break 'v virtasm_transform_expr(
                            data,
                            globals_map,
                            toplevel_var_types,
                            *e2,
                            let_bound,
                        );
                    }
                }
            }
            let mut e1 = virtasm_transform_expr(
                data,
                globals_map,
                toplevel_var_types,
                *e1,
                LetBound::from_vardef(d),
            );
            e1.assign(Cow::Owned(name), ty.as_concty().unwrap(), None);
            let e2 = virtasm_transform_expr(data, globals_map, toplevel_var_types, *e2, let_bound);
            e1.concat(e2)
        }
        IrNode::Var(VarDef { name, ty }) => {
            if toplevel_var_types.contains_key(&name) {
                tail!(LoadLabelAddr(Label::Ident(name)))
            } else {
                match ty.as_concty().unwrap() {
                    ConcTy::Unit => tail!(Nop),
                    ConcTy::Float => tail!(MovF(V(FVReg(name)))),
                    _ => tail!(Mov(V(IVReg(name)))),
                }
            }
        }
        IrNode::ApplyDirectly(l, ys) => {
            let loads = get_from_globals(ys.iter(), toplevel_var_types);

            let len = ys.len();
            let mut intargs = Vec::with_capacity(len);
            let mut floatargs = Vec::with_capacity(len);
            for VarDef { mut name, ty } in ys {
                loads.rename_var(&mut name);
                let t = ty.as_concty().unwrap();
                match t {
                    ConcTy::Unit => (),
                    ConcTy::Float => floatargs.push(FVReg(name)),
                    _ => intargs.push(IVReg(name)),
                };
            }
            tail!(loads.stmts.into(), CallDirectly(l, intargs, floatargs))
        }
        IrNode::Tuple(xs) => {
            let y = Ident::new();
            let mut assign_before = Vec::new();
            let mut store = Vec::with_capacity(xs.len());
            let mut offset = 0;
            let ts: Vec<_> = xs.iter().map(|x| (x.get_concty())).collect();
            for x in xs.into_iter() {
                let y = IVReg(y.clone());
                match x {
                    Variable(VarDef { name, ty }) => match ty.as_concty().unwrap() {
                        ConcTy::Unit => (),
                        ConcTy::Float => {
                            store.push(Stmt::StoreF(V(FVReg(name)), V(y), offset));
                            offset += 1;
                        }
                        _ => {
                            store.push(Stmt::Store(V(IVReg(name)), V(y), offset));
                            offset += 1;
                        }
                    },
                    Constant(c) => match ConstSource::from_const(c) {
                        ConstSource::Int(i) => match i {
                            IConstSource::Value(i) => {
                                let name = Ident::uniq_name("tuple_elemi");
                                assign_before.push(assign(
                                    Cow::Borrowed(&name),
                                    ConcTy::Int,
                                    LoadInt(i),
                                ));
                                store.push(Stmt::StoreF(V(FVReg(name)), V(y), offset));
                                offset += 1;
                            }
                            IConstSource::Register(r) => {
                                store.push(Stmt::Store(P(r), V(y), offset));
                                offset += 1;
                            }
                        },
                        ConstSource::Float(f) => match f {
                            FConstSource::MovF(r) => {
                                store.push(Stmt::StoreF(P(r), V(y), offset));
                                offset += 1;
                            }
                            f => {
                                let name = Ident::uniq_name("tuple_elemf");
                                assign_before.push(assign(
                                    Cow::Borrowed(&name),
                                    ConcTy::Float,
                                    match f {
                                        FConstSource::Value(f) => float_constant(f, data),
                                        FConstSource::Fneg(f) => {
                                            Expr::FUnOp(ast::FUnOpKind::Fneg, P(f))
                                        }
                                        FConstSource::MovF(_) => unreachable!(),
                                    },
                                ));
                                store.push(Stmt::StoreF(V(FVReg(name)), V(y), offset));
                                offset += 1;
                            }
                        },
                    },
                }
            }
            let mut before_store: Vec<_> = assign_before
                .into_iter()
                .chain([
                    assign(Cow::Borrowed(&y), ConcTy::Tuple(ts), Mov(P(REG_HP))),
                    IncrABI(REG_HP, offset),
                ])
                .collect();
            before_store.extend(store);
            FlatExprs::tail(FlatExpr::anorm(before_store, Mov(V(IVReg(y)))))
        }
        IrNode::Get(VarDef { name: x, ty }, Variable(y)) => {
            let ConcTy::Array(ty, ..) = ty.as_concty().unwrap() else {
                panic!("invalid ty for an array (Get)")
            };
            match *ty {
                ConcTy::Unit => tail!(Expr::Nop),
                _ => {
                    let addr = Ident::new();

                    FlatExprs::tail(FlatExpr::anorm(
                        [assign(
                            Cow::Borrowed(&addr),
                            ConcTy::Int,
                            Expr::IBinOp(IBinOpKind::Add, IVReg(x), SymbOrImm::Sym(IVReg(y))),
                        )],
                        Expr::Load(V(IVReg(addr)), 0),
                    ))
                }
            }
        }
        IrNode::Get(VarDef { name: x, ty }, Constant(i)) => {
            let ty = ty
                .as_concty()
                .unwrap()
                .as_nth(*i.as_int().unwrap() as usize)
                .unwrap();
            match ty {
                ConcTy::Unit => tail!(Expr::Nop),
                _ => {
                    tail!(Expr::Load(V(IVReg(x)), *i.as_int().unwrap()))
                }
            }
        }
        IrNode::GetGlobal(x, Variable(y)) => {
            let ConcTy::Array(ty, ..) = toplevel_var_types.get(&x).unwrap().as_concty().unwrap()
            else {
                panic!("invalid ty for an array (Get)")
            };
            match *ty {
                ConcTy::Unit => tail!(Nop),
                _ => tail!(LoadFromLabelDisp(Some(V(IVReg(y))), Label::Ident(x), 0)),
            }
        }
        IrNode::GetGlobal(x, Constant(i)) => {
            let ty = toplevel_var_types
                .get(&x)
                .unwrap()
                .as_concty()
                .unwrap()
                .as_nth(*i.as_int().unwrap() as usize)
                .unwrap();
            match ty {
                ConcTy::Unit => tail!(Nop),
                _ => {
                    tail!(LoadFromLabelDisp(
                        None,
                        Label::Ident(x),
                        *i.as_int().unwrap()
                    ))
                }
            }
        }
        IrNode::Set(VarDef { name: x, ty }, Variable(y), z) => {
            let ConcTy::Array(ty, ..) = ty.as_concty().unwrap() else {
                panic!("invalid ty for an array (Set)")
            };
            match RegKind::from_concty(&ty) {
                None => tail!(Expr::Nop),
                Some(s) => {
                    let addr = Ident::uniq_name("addr");
                    let st = match s {
                        RegKind::Int => Store(V(IVReg(z)), V(IVReg(addr.clone())), 0),
                        RegKind::Float => StoreF(V(FVReg(z)), V(IVReg(addr.clone())), 0),
                    };

                    tail_stmt!([
                        assign(
                            Cow::Owned(addr),
                            ConcTy::Int,
                            IBinOp(IBinOpKind::Add, IVReg(x), SymbOrImm::Sym(IVReg(y))),
                        ),
                        st
                    ])
                }
            }
        }
        IrNode::Set(VarDef { name: x, ty }, Constant(i), z) => {
            let ty = ty
                .as_concty()
                .unwrap()
                .as_nth(*i.as_int().unwrap() as usize)
                .unwrap();
            match RegKind::from_concty(&ty) {
                None => tail!(Nop),
                Some(s) => {
                    let disp = *i.as_int().unwrap();
                    let st = match s {
                        RegKind::Int => Store(V(IVReg(z)), V(IVReg(x)), disp),
                        RegKind::Float => StoreF(V(FVReg(z)), V(IVReg(x)), disp),
                    };
                    tail_stmt!([st])
                }
            }
        }
        IrNode::SetGlobal(x, Variable(y), z) => {
            let ConcTy::Array(ty, ..) = toplevel_var_types.get(&x).unwrap().as_concty().unwrap()
            else {
                panic!("invalid ty for an array (Set)")
            };
            match RegKind::from_concty(&ty) {
                None => tail!(Expr::Nop),
                Some(s) => {
                    let st = match s {
                        RegKind::Int => {
                            StoreLabelDisp(V(IVReg(z)), Some(V(IVReg(y))), Label::Ident(x), 0)
                        }
                        RegKind::Float => {
                            StoreFLabelDisp(V(FVReg(z)), Some(V(IVReg(y))), Label::Ident(x), 0)
                        }
                    };
                    tail_stmt!([st])
                }
            }
        }
        IrNode::SetGlobal(x, Constant(i), z) => {
            let ty = toplevel_var_types
                .get(&x)
                .unwrap()
                .as_concty()
                .unwrap()
                .as_nth(*i.as_int().unwrap() as usize)
                .unwrap();
            match RegKind::from_concty(&ty) {
                None => tail!(Nop),
                Some(s) => {
                    let disp = *i.as_int().unwrap();
                    let st = match s {
                        RegKind::Int => StoreLabelDisp(V(IVReg(z)), None, Label::Ident(x), disp),
                        RegKind::Float => StoreFLabelDisp(V(FVReg(z)), None, Label::Ident(x), disp),
                    };
                    tail_stmt!([st])
                }
            }
        }
        IrNode::ArrayMake(Constant(count), value) => {
            let count = *count.as_int().unwrap();
            let let_bound = let_bound.unwrap();
            let arr_name = let_bound.name.as_i().unwrap();
            match value {
                Variable(VarDef { name: v, ty }) => {
                    match abi::RegKind::from_concty(&ty.as_concty().unwrap()).unwrap() {
                        abi::RegKind::Int => FlatExprs::tail(FlatExpr::extra2(
                            Mov(P(REG_HP)),
                            std::iter::once(IncrABI(REG_HP, count)).chain((0..count).map(|c| {
                                let addr = c;
                                Store(V(IVReg(v.clone())), V(arr_name.clone()), addr)
                            })),
                        )),
                        abi::RegKind::Float => FlatExprs::tail(FlatExpr::extra2(
                            Mov(P(REG_HP)),
                            std::iter::once(IncrABI(REG_HP, count)).chain((0..count).map(|c| {
                                let addr = c;
                                StoreF(V(FVReg(v.clone())), V(arr_name.clone()), addr)
                            })),
                        )),
                    }
                }
                Constant(i) => {
                    use ConstSource::*;
                    match ConstSource::from_const(i) {
                        Int(IConstSource::Value(i)) => {
                            let array_init_val = Ident::ubiq_name("elem");
                            FlatExprs::tail(FlatExpr::extra2(
                                Mov(P(REG_HP)),
                                std::iter::once(IncrABI(REG_HP, count))
                                    .chain(std::iter::once(assign(
                                        Cow::Borrowed(&array_init_val),
                                        ConcTy::Int,
                                        LoadInt(i),
                                    )))
                                    .chain((0..count).map(|c| {
                                        let addr = c;
                                        Store(
                                            V(IVReg(array_init_val.clone())),
                                            V(arr_name.clone()),
                                            addr,
                                        )
                                    })),
                            ))
                        }
                        Int(IConstSource::Register(r)) => FlatExprs::tail(FlatExpr::extra2(
                            Mov(P(REG_HP)),
                            std::iter::once(IncrABI(REG_HP, count)).chain((0..count).map(|c| {
                                let addr = c;
                                Store(P(r), V(arr_name.clone()), addr)
                            })),
                        )),
                        Float(FConstSource::MovF(r)) => FlatExprs::tail(FlatExpr::extra2(
                            Mov(P(REG_HP)),
                            std::iter::once(IncrABI(REG_HP, count)).chain((0..count).map(|c| {
                                let addr = c;
                                StoreF(P(r), V(arr_name.clone()), addr)
                            })),
                        )),
                        Float(f) => {
                            let array_init_val = Ident::ubiq_name("elem");
                            FlatExprs::tail(FlatExpr::extra2(
                                Mov(P(REG_HP)),
                                std::iter::once(IncrABI(REG_HP, count))
                                    .chain(std::iter::once(assign(
                                        Cow::Borrowed(&array_init_val),
                                        ConcTy::Float,
                                        match f {
                                            FConstSource::Value(f) => float_constant(f, data),
                                            FConstSource::Fneg(f) => {
                                                Expr::FUnOp(ast::FUnOpKind::Fneg, P(f))
                                            }
                                            FConstSource::MovF(_) => unreachable!(),
                                        },
                                    )))
                                    .chain((0..count).map(|c| {
                                        let addr = c;
                                        StoreF(
                                            V(FVReg(array_init_val.clone())),
                                            V(arr_name.clone()),
                                            addr,
                                        )
                                    })),
                            ))
                        }
                    }
                }
            }
        }
        IrNode::ArrayMake(Variable(count), value) => {
            let mut before = StmtList::new();
            let (value, ty) = match value {
                Variable(VarDef { name, ty }) => {
                    if toplevel_var_types.contains_key(&name) {
                        before.push_back(assign(
                            Cow::Borrowed(&name),
                            ty.as_concty().unwrap(),
                            LoadLabelAddr(Label::Ident(name.clone())),
                        ))
                    }
                    (
                        name,
                        RegKind::from_concty(&ty.as_concty().unwrap())
                            .expect("do not create array of unit"),
                    )
                }
                Constant(c) => {
                    let value = Ident::uniq_name("init_value");
                    match c {
                        ConstKind::Unit => todo!(),
                        ConstKind::Bool(_) => todo!(),
                        ConstKind::Int(i) => {
                            before.push_back(assign(
                                Cow::Borrowed(&value),
                                ConcTy::Int,
                                LoadInt(i),
                            ));
                            (value, RegKind::Int)
                        }
                        ConstKind::Float(f) => {
                            before.push_back(assign(
                                Cow::Borrowed(&value),
                                ConcTy::Float,
                                float_constant(f, data),
                            ));
                            (value, RegKind::Int)
                        }
                    }
                }
            };
            match ty {
                RegKind::Int => tail!(
                    before,
                    CallDirectly(
                        Label::raw_name(".create_array_int"),
                        vec![IVReg(count), IVReg(value)],
                        vec![],
                    )
                ),
                RegKind::Float => {
                    tail!(
                        before,
                        CallDirectly(
                            Label::raw_name(".create_array_float"),
                            vec![IVReg(count)],
                            vec![FVReg(value)]
                        )
                    )
                }
            }
        }
        IrNode::Pervasive(name, args) => {
            let mut iargs = Vec::new();
            let mut fargs = Vec::new();
            for (x, t) in args
                .into_iter()
                .zip(V_ASM_PERVASIVES.get(name).unwrap().sig.get_ty().arg)
            {
                match t {
                    ConcTy::Unit => (),
                    ConcTy::Float => fargs.push(FVReg(x)),
                    _ => iargs.push(IVReg(x)),
                };
            }
            tail!(Intrinsic(name.to_string(), iargs, fargs))
        }
        IrNode::BBinOp(op, x, y) => tail!(BBinOp(op, IVReg(x), IVReg(y))),
        IrNode::PrintInt(Variable(c)) => {
            tail!(CallDirectly(
                Label::raw_name(".print_int"),
                vec![IVReg(c)],
                vec![]
            ))
        }
        IrNode::PrintInt(Constant(c)) => {
            let s = c.to_string();
            let it = s.as_bytes().iter().flat_map(|byte| {
                let c = Ident::uniq_name("byte");
                [
                    assign(Cow::Borrowed(&c), ConcTy::Int, LoadInt(*byte as i32)),
                    discard(Intrinsic("print_char".to_string(), vec![IVReg(c)], vec![])),
                ]
            });
            tail_stmt!(it)
        }
        IrNode::Loop(Continue(label, assigns), e) => {
            let loads = get_from_globals(assigns.iter().map(|(_, p)| p), toplevel_var_types);
            let e = virtasm_transform_expr(
                data,
                globals_map,
                toplevel_var_types,
                *e,
                let_bound.clone(),
            );
            let endloop_label = Label::name("end_loop");
            let tail = FlatExprs::tail(FlatExpr::LoopBranch {
                loop_label: Label::Ident(label),
                loop_init_param: assigns
                    .into_iter()
                    .map(|(l, r)| {
                        let mut rhs = IorF::from_vardef(Cow::Owned(r)).unwrap();
                        loads.rename_var(&mut rhs);
                        BlockParamAssign::from_assign(LetBound::from_vardef(l).unwrap(), rhs)
                    })
                    .collect(),
                loop_br: let_bound.clone().map(BlockParamAssign::new),
                body: e,
                endloop_label,
                lb: let_bound,
                coalesced: false,
            });
            FlatExprs::seq(loads.stmts, tail)
        }
        IrNode::Continue(Continue(label, assigns)) => {
            let loads = get_from_globals(assigns.iter().map(|(_, p)| p), toplevel_var_types);
            let tail = FlatExprs::tail(FlatExpr::Continue {
                br: Terminator::Branch(Branch(
                    Label::Ident(label),
                    assigns
                        .into_iter()
                        .map(|(l, r)| {
                            let mut rhs = IorF::from_vardef(Cow::Owned(r)).unwrap();
                            loads.rename_var(&mut rhs);
                            BlockParamAssign::from_assign(LetBound::from_vardef(l).unwrap(), rhs)
                        })
                        .collect(),
                )),
            });
            FlatExprs::seq(loads.stmts, tail)
        }
    }
}

struct LoadFromGlobal<'a> {
    stmts: Vec<Stmt<Label<'a>, IVReg<'a>, FVReg<'a>>>,
    rename_map: HashMap<IdentSymbol, Ident<'a>>,
}

impl<'a> LoadFromGlobal<'a> {
    fn rename_var(&self, var: &mut Ident<'a>) {
        if let Some(renamed) = self.rename_map.get(var.id()) {
            *var = renamed.to_owned();
        }
    }
}

/// globals doesn't have their definition, so we replace all uses of them
/// with renamed one. variable **MUST** be renamed in order to maintain SSA.
fn get_from_globals<'a: 'b, 'b>(
    assigns: impl Iterator<Item = &'b VarDef<'a>>,
    toplevel_var_types: &HashMap<Ident<'a>, ty::Ty>,
) -> LoadFromGlobal<'a> {
    let (stmts, rename_map) = assigns
        .filter_map(|vd| {
            if toplevel_var_types.contains_key(&vd.name) {
                let renamed = vd.name.updated();
                Some((
                    assign(
                        Cow::Borrowed(&renamed),
                        vd.ty.as_concty().unwrap(),
                        Expr::LoadLabelAddr(Label::Ident(vd.name.to_owned())),
                    ),
                    (*vd.name.id(), renamed),
                ))
            } else {
                None
            }
        })
        .unzip();
    LoadFromGlobal { stmts, rename_map }
}

fn virtasm_transform_fundef<'a>(
    data: &mut FloatConstMap<Label<'a>>,
    globals_map: &mut GlobalVarMap<Ident<'a>>,
    global_var_types: &HashMap<Ident<'a>, ty::Ty>,
    ir_closure::FunDef {
        name: VarDef { name: x, ty: t },
        args,
        captured_vars,
        body: e,
    }: ir_closure::FunDef<'a>,
) -> VAsmFunDef<'a> {
    let l = args.len();
    let mut iargs = Vec::with_capacity(l);
    let mut fargs = Vec::with_capacity(l);
    for VarDef { name, ty } in args {
        let cty = ty.as_concty().unwrap();
        match cty {
            ConcTy::Unit => (),
            ConcTy::Float => fargs.push((FVReg(name), cty)),
            _ => iargs.push((IVReg(name), cty)),
        };
    }
    let inner_e =
        virtasm_transform_expr(data, globals_map, global_var_types, *e, LetBoundKind::None);
    assert!(captured_vars.is_empty());
    let body = inner_e;
    match t.as_concty().unwrap() {
        ConcTy::Fun(_, t2) => {
            let name = Label::Ident(x);
            let ret = *t2;
            let bb = body.into_bb(ret.clone());
            FunDef {
                name,
                args: iargs,
                fargs,
                body: bb,
                ret,
            }
        }
        _ => unreachable!(),
    }
}

fn eval_constant_ctxt<'a>(
    globals_map: &mut GlobalVarMap<Ident<'a>>,
    e: &IrNode<'a>,
    ty: &mut ty::ConcTy,
) -> Option<GlobalVarValue<Ident<'a>>> {
    use CompileTimeConst::*;
    use GlobalVarValue::*;
    use MaybeConst::*;
    match e {
        IrNode::Var(v) => {
            let g = globals_map.get(&v.name)?;
            Some(g.value.clone())
        }
        IrNode::Tuple(t) => {
            let mut v = Vec::new();
            for t in t {
                v.push(match t {
                    Variable(VarDef { name, ty: _ }) => {
                        if !globals_map.contains_key(name) {
                            return None;
                        }
                        AddressOf(name.clone())
                    }
                    Constant(c) => CompileTimeConst::try_from_constkind(*c)?,
                });
            }
            Some(Tuple(v))
        }
        IrNode::ArrayMake(Constant(c), Constant(v)) => {
            let c = *c.as_int().unwrap();
            if let ConcTy::Array(_, l) = ty {
                *l = Some(c as usize);
            };
            Some(Array(GlobalVarArray::new(
                c,
                match v {
                    ConstKind::Int(i) => Int(*i),
                    ConstKind::Float(f) => Float(*f),
                    _ => unreachable!(),
                },
            )))
        }
        IrNode::ArrayMake(Constant(c), Variable(v)) => {
            let c = *c.as_int().unwrap();
            if let ConcTy::Array(_, l) = ty {
                *l = Some(c as usize);
            };
            Some(Array(GlobalVarArray::new(c, AddressOf(v.name.clone()))))
        }
        IrNode::GetGlobal(x, Constant(c)) => {
            let g = globals_map.get(x)?;
            let a = g.value.as_array().unwrap();
            Some(Const(a.get(c.as_int().unwrap()).clone()))
        }
        IrNode::SetGlobal(x, Constant(c), i) if globals_map.contains_key(i) => {
            globals_map
                .get_mut(x)?
                .value
                .as_array_mut()
                .unwrap()
                .modification
                .insert(*c.as_int().unwrap(), AddressOf(i.clone()));
            None
        }
        _ => None,
    }
}

pub fn asmv_transform(
    ir_closure::Prog {
        fundefs,
        tail_expr,
        toplevel_var_types,
    }: ir_closure::Prog,
) -> VirtualAsm {
    let mut float_map = HashMap::new();
    let mut globals_map = GlobalVarMap::new();
    let entrypoint = Label::uniq_name("main");
    let mut fundefs: Vec<_> = fundefs
        .into_iter()
        .map(|u| virtasm_transform_fundef(&mut float_map, &mut globals_map, &toplevel_var_types, u))
        .collect();
    let e = virtasm_transform_expr(
        &mut float_map,
        &mut globals_map,
        &toplevel_var_types,
        tail_expr,
        LetBoundKind::None,
    );
    let mut bbs = e.into_bb(ConcTy::Unit);
    for bb in bbs.iter_mut() {
        bb.exit_program();
    }
    let main_f = FunDef {
        name: entrypoint.clone(),
        args: vec![],
        fargs: vec![],
        body: bbs,
        ret: ConcTy::Unit,
    };
    fundefs.push(main_f);
    Prog {
        float_map,
        globals_map,
        fundefs,
        entry_point: entrypoint,
    }
}
