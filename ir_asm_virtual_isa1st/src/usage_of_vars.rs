use std::collections::HashMap;

use ir_asm_virtual_ast_isa1st::{
    Branch, CondBr, CondBrKind, Expr, FVReg, IVReg, LetBound, Stmt, SymbOrImm, Terminator,
    VAsmFunDef,
};
use typedefs::{IdentSymbol, Label};

pub trait Collectable {
    /// collect usage of variable.
    /// variable used only once can easily be inlined into caller.
    ///
    /// this method is path-insensitive.
    fn collect_usage(&self, c: &mut CollectUsage);
}

#[derive(Default)]
pub struct CollectUsage {
    usage_of_var: HashMap<IdentSymbol, usize>,
}

impl CollectUsage {
    fn def_of_var(&mut self, name: &IdentSymbol) {
        self.usage_of_var.entry(*name).or_insert(0);
    }
    pub fn use_of_var(&mut self, name: &IdentSymbol) {
        self.usage_of_var
            .entry(*name)
            .and_modify(|c| *c += 1)
            .or_insert(1);
    }
    pub fn is_used_once(&self, name: &IdentSymbol) -> bool {
        self.usage_of_var.get(name) == Some(&1)
    }
    pub fn is_used(&self, name: &IdentSymbol) -> bool {
        self.usage_of_var.get(name).is_some_and(|c| c != &0)
    }
    pub fn usage_of_var(&self) -> &HashMap<IdentSymbol, usize> {
        &self.usage_of_var
    }

    pub fn clear(&mut self) {
        self.usage_of_var.clear()
    }
}

impl Collectable for VAsmFunDef<'_> {
    fn collect_usage(&self, c: &mut CollectUsage) {
        for bb in &self.body {
            for LetBound { name, ty: _ } in &bb.block_param {
                c.def_of_var(name);
            }
            for instr in &bb.instrs {
                instr.collect_usage(c);
            }
            bb.terminator.collect_usage(c);
        }
    }
}

impl<'a> Collectable for Stmt<Label<'a>, IVReg<'a>, FVReg<'a>> {
    fn collect_usage(&self, c: &mut CollectUsage) {
        match self {
            Stmt::IncrABI(..) => (),
            Stmt::Assign(d, _, u) => {
                if let Some(d) = d {
                    c.def_of_var(d);
                }
                match u {
                    Expr::Load(i, _) | Expr::Mov(i) | Expr::LoadFromLabelDisp(Some(i), ..) => {
                        if let Some(i) = i.as_v() {
                            c.use_of_var(i);
                        }
                    }
                    Expr::IUnOp(_, i) => {
                        c.use_of_var(i);
                    }
                    Expr::MovF(f) => {
                        if let Some(f) = f.as_v() {
                            c.use_of_var(f);
                        }
                    }
                    Expr::FUnOp(_, f) => {
                        if let Some(f) = f.as_v() {
                            c.use_of_var(f);
                        }
                    }
                    Expr::BBinOp(_, i1, i2) => {
                        c.use_of_var(i1);
                        c.use_of_var(i2);
                    }
                    Expr::IBinOp(_, i1, i2) => {
                        c.use_of_var(i1);
                        if let SymbOrImm::Sym(i2) = i2 {
                            c.use_of_var(i2);
                        }
                    }
                    Expr::FBinOp(_, f1, f2) => {
                        if let Some(f) = f1.as_v() {
                            c.use_of_var(f);
                        }
                        if let Some(f) = f2.as_v() {
                            c.use_of_var(f);
                        }
                    }
                    Expr::FTerOp(_, f1, f2, f3) => {
                        if let Some(f) = f1.as_v() {
                            c.use_of_var(f);
                        }
                        if let Some(f) = f2.as_v() {
                            c.use_of_var(f);
                        }
                        if let Some(f) = f3.as_v() {
                            c.use_of_var(f);
                        }
                    }
                    Expr::CallDirectly(_, is, fs) => {
                        for i in is {
                            c.use_of_var(i);
                        }
                        for f in fs {
                            c.use_of_var(f);
                        }
                    }
                    Expr::Intrinsic(_, is, fs) => {
                        for i in is {
                            c.use_of_var(i);
                        }
                        for f in fs {
                            c.use_of_var(f);
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
                    c.use_of_var(u);
                }
                if let Some(u) = pv2.as_v() {
                    c.use_of_var(u);
                }
            }
            Stmt::StoreF(pv1, pv2, _) => {
                if let Some(u) = pv1.as_v() {
                    c.use_of_var(u);
                }
                if let Some(u) = pv2.as_v() {
                    c.use_of_var(u);
                }
            }
            Stmt::StoreLabelDisp(i, i1, ..) => {
                if let Some(i) = i1.as_ref().and_then(|i| i.as_v()) {
                    c.use_of_var(i);
                }
                if let Some(i) = i.as_v() {
                    c.use_of_var(i);
                }
            }
            Stmt::StoreFLabelDisp(f, i1, ..) => {
                if let Some(i) = i1.as_ref().and_then(|i| i.as_v()) {
                    c.use_of_var(i);
                }
                if let Some(f) = f.as_v() {
                    c.use_of_var(f);
                }
            }
        }
    }
}

impl<'a> Collectable for Terminator<IVReg<'a>, FVReg<'a>, Label<'a>> {
    fn collect_usage(&self, c: &mut CollectUsage) {
        match self {
            Terminator::Exit | Terminator::End => (),
            Terminator::Ret(u) => {
                c.use_of_var(u);
            }
            Terminator::Branch(Branch(_, us)) => {
                for i in us {
                    c.use_of_var(i.rhs());
                }
            }
            Terminator::CondBr(CondBr(cdbr, ..)) => match cdbr {
                CondBrKind::IfBin(_, u1, u2, ..) => {
                    c.use_of_var(u1);
                    if let Some(u2) = u2.as_ident() {
                        c.use_of_var(u2);
                    }
                }
                CondBrKind::IfBinF(_, u1, u2, ..) => {
                    if let Some(f) = u1.as_v() {
                        c.use_of_var(f);
                    }
                    if let Some(f) = u2.as_v() {
                        c.use_of_var(f);
                    }
                }
                CondBrKind::IfUn(_, u, ..) => {
                    c.use_of_var(u);
                }
                CondBrKind::IfUnF(_, u, ..) => {
                    if let Some(f) = u.as_v() {
                        c.use_of_var(f);
                    }
                }
            },
            Terminator::TailCall(_, is, fs) => {
                for i in is {
                    c.use_of_var(i);
                }
                for f in fs {
                    c.use_of_var(f);
                }
            }
        }
    }
}
