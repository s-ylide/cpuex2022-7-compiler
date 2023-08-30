#![feature(if_let_guard)]

mod alpha_convert;
mod beta_convert;
mod const_folding;
mod create_loop;
mod cse;
mod destruct_tuple;
mod elim_unused;
mod find_static_alias;
mod find_unused_let;
mod flatten_let;
mod inlining;
mod transform;
pub use alpha_convert::alpha_convert;
pub use beta_convert::beta_convert;
pub use const_folding::const_folding;
pub use create_loop::create_loop;
pub use cse::elim_common_expr;
pub use destruct_tuple::destruct_tuple;
pub use elim_unused::elim_unused;
pub use find_static_alias::find_static_alias;
pub use find_unused_let::find_unused_let;
pub use flatten_let::flatten_let;
pub use inlining::inlining;
pub use transform::knorm_transform;

use ast::{BBinOpKind, ConstKind, FBinOpKind, FTerOpKind, FUnOpKind, IBinOpKind, IUnOpKind};
use pervasives::V_ASM_PERVASIVES;
use std::collections::HashMap;
use std::fmt::Write;
use std::{cell::RefCell, fmt::Display, rc::Rc};
use typedefs::{CanbeConst, Ident, IdentSymbol, IfBranch, IfCond, IfExpr, MaybeConst, VarDef};
use util::indented::Indented;

#[derive(Debug, Clone)]
pub struct Continue<'a>(pub Ident<'a>, pub Vec<(VarDef<'a>, VarDef<'a>)>);

#[derive(Debug)]
pub enum IrNode<'a> {
    Const(ConstKind),
    IUnOp(IUnOpKind, Ident<'a>),
    BBinOp(BBinOpKind, Ident<'a>, Ident<'a>),
    IBinOp(IBinOpKind, Ident<'a>, MaybeConst<Ident<'a>>),
    FUnOp(FUnOpKind, Ident<'a>),
    FBinOp(FBinOpKind, Ident<'a>, Ident<'a>),
    FTerOp(FTerOpKind, Ident<'a>, Ident<'a>, Ident<'a>),
    If(IfExpr<VarDef<'a>, Ident<'a>, Rc<RefCell<Self>>>),
    Let(VarDef<'a>, Rc<RefCell<Self>>, Rc<RefCell<Self>>),
    LetRec(FunDef<'a>, Rc<RefCell<Self>>),
    LetTuple(Vec<VarDef<'a>>, VarDef<'a>, Rc<RefCell<Self>>),
    Var(VarDef<'a>),
    App(Ident<'a>, Vec<CanbeConst<VarDef<'a>>>),
    Tuple(Vec<MaybeConst<VarDef<'a>>>),
    Get(VarDef<'a>, MaybeConst<Ident<'a>>),
    Set(VarDef<'a>, MaybeConst<Ident<'a>>, VarDef<'a>),
    /// `val make : int -> 'a -> 'a array`
    ArrayMake(MaybeConst<Ident<'a>>, MaybeConst<VarDef<'a>>),
    PrintInt(MaybeConst<Ident<'a>>),
    Pervasive(ast::Ident<'a>, Vec<CanbeConst<VarDef<'a>>>),
    Loop(Continue<'a>, Rc<RefCell<Self>>),
    Continue(Continue<'a>),
}

impl<'a> IrNode<'a> {
    pub fn len(&self) -> usize {
        let mut len = 0;
        enum Stack<'a, 'b> {
            Root(&'b IrNode<'a>),
            Walk(Rc<RefCell<IrNode<'a>>>),
        }
        let mut stack: Vec<Stack> = Vec::new();
        use Stack::*;
        stack.push(Root(self));
        fn mu<'a, 'b>(r: &Rc<RefCell<IrNode<'a>>>) -> Stack<'a, 'b> {
            Walk(r.clone())
        }
        while let Some(node) = stack.pop() {
            len += 1;
            match node {
                Root(r) => visit_node(r, &mut stack),
                Walk(w) => visit_node(&w.borrow(), &mut stack),
            }
            fn visit_node<'a>(r: &IrNode<'a>, stack: &mut Vec<Stack<'a, '_>>) {
                match r {
                    IrNode::Let(_, e1, e2) => {
                        stack.push(mu(e2));
                        stack.push(mu(e1));
                    }
                    IrNode::If(IfExpr {
                        clauses:
                            IfBranch::ThenElse {
                                then_: e1,
                                else_: e2,
                            },
                        ..
                    }) => {
                        stack.push(mu(e2));
                        stack.push(mu(e1));
                    }
                    IrNode::LetRec(.., e) | IrNode::LetTuple(.., e) | IrNode::Loop(.., e) => {
                        stack.push(mu(e));
                    }
                    _ => (),
                }
            }
        }
        len
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<'a> Display for Continue<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Continue(label, is) = self;
        write!(
            f,
            "'{label} with ({})",
            is.iter()
                .map(|(p, i)| format!("{p} := {i}"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl<'a> Display for IrNode<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut f = Indented::new(f, "  ");
        self.fmt_indented(&mut f, false)
    }
}

impl<'a> IrNode<'a> {
    fn fmt_indented(
        &self,
        f: &mut Indented<std::fmt::Formatter<'_>>,
        newline_let: bool,
    ) -> std::fmt::Result {
        fn fmt_if_indented(
            f: &mut Indented<std::fmt::Formatter>,
            e1: &Rc<RefCell<IrNode>>,
            e2: &Rc<RefCell<IrNode>>,
        ) -> Result<(), std::fmt::Error> {
            f.indent(1);
            writeln!(f)?;
            e1.borrow().fmt_indented(f, false)?;
            f.dedent(1);
            writeln!(f)?;
            write!(f, "}} else {{")?;
            f.indent(1);
            writeln!(f)?;
            e2.borrow().fmt_indented(f, false)?;
            f.dedent(1);
            writeln!(f)?;
            write!(f, "}}")
        }
        fn fmt_args<T: Display>(is: &[T]) -> String {
            let v = is.iter().map(|i| format!("{i}")).collect::<Vec<_>>();
            if v.is_empty() {
                "()".to_string()
            } else {
                v.join(" ")
            }
        }

        match self {
            IrNode::Const(c) => write!(f, "{c}"),
            IrNode::IUnOp(op, i) => match op {
                IUnOpKind::Not => write!(f, "!{i}"),
                IUnOpKind::Neg => write!(f, "-{i}"),
                IUnOpKind::ItoF => write!(f, "itof {i}"),
            },
            IrNode::BBinOp(..) => todo!(),
            IrNode::IBinOp(op, i1, i2) => {
                let symb = op.symbol();
                write!(f, "{i1} {symb} {i2}")
            }
            IrNode::FUnOp(op, i) => match op {
                FUnOpKind::Fneg => write!(f, "-{i}"),
                FUnOpKind::Sqrt => write!(f, "sqrt {i}"),
                FUnOpKind::Floor => write!(f, "floor {i}"),
                FUnOpKind::Finv => write!(f, "finv {i}"),
                FUnOpKind::Ftoi => write!(f, "ftoi {i}"),
                FUnOpKind::Fiszero => write!(f, "{i} == 0.0"),
                FUnOpKind::Fispos => write!(f, "{i} > 0.0"),
                FUnOpKind::Fisneg => write!(f, "{i} < 0.0"),
            },
            IrNode::FBinOp(op, i1, i2) => {
                let symb = match op {
                    FBinOpKind::FAdd => "+.",
                    FBinOpKind::FSub => "-.",
                    FBinOpKind::FMul => "*.",
                    FBinOpKind::FDiv => "/.",
                    FBinOpKind::Fless => "<",
                };
                write!(f, "{i1} {symb} {i2}")
            }
            IrNode::FTerOp(op, i1, i2, i3) => match op {
                FTerOpKind::Fmadd => write!(f, "{i1} *. {i2} +. {i3}"),
                FTerOpKind::Fmsub => write!(f, "{i1} *. {i2} -. {i3}"),
                FTerOpKind::Fnmadd => write!(f, "-{i1} *. {i2} +. {i3}"),
                FTerOpKind::Fnmsub => write!(f, "-{i1} *. {i2} -. {i3}"),
            },
            IrNode::If(IfExpr { cond, clauses }) => {
                write!(f, "if {cond} {{")?;
                match clauses {
                    IfBranch::ThenElse { then_, else_ } => fmt_if_indented(f, then_, else_),
                }
            }
            IrNode::Let(def, e1, e2) => {
                if newline_let {
                    f.indent(1);
                    writeln!(f)?;
                }
                write!(f, "let {}: {} = ", def.name, def.ty.as_concty().unwrap(),)?;
                e1.borrow().fmt_indented(f, true)?;
                writeln!(f, " in")?;
                e2.borrow().fmt_indented(f, false)?;
                if newline_let {
                    f.dedent(1);
                }
                Ok(())
            }
            IrNode::LetRec(fundef, e) => {
                if newline_let {
                    f.indent(1);
                    writeln!(f)?;
                }
                write!(
                    f,
                    "let rec {} {} = ",
                    fundef.var.name,
                    fundef
                        .args
                        .iter()
                        .map(|VarDef { name, ty }| format!("({name}: {})", ty.as_concty().unwrap()))
                        .collect::<Vec<_>>()
                        .join(" "),
                )?;
                fundef.body.borrow().fmt_indented(f, true)?;
                writeln!(f)?;
                writeln!(f, "in")?;
                e.borrow().fmt_indented(f, false)?;
                if newline_let {
                    f.dedent(1);
                }
                Ok(())
            }
            IrNode::LetTuple(defs, i, e) => {
                if newline_let {
                    f.indent(1);
                    writeln!(f)?;
                }
                writeln!(
                    f,
                    "let ({}) = {i} in",
                    defs.iter()
                        .map(|VarDef { name, ty }| format!("({name}: {})", ty.as_concty().unwrap()))
                        .collect::<Vec<_>>()
                        .join(", "),
                )?;
                e.borrow().fmt_indented(f, false)?;
                if newline_let {
                    f.dedent(1);
                }
                Ok(())
            }
            IrNode::Loop(c, e) => {
                if newline_let {
                    f.indent(1);
                    writeln!(f)?;
                }
                write!(f, "loop {c} {{",)?;
                f.indent(1);
                writeln!(f)?;
                e.borrow().fmt_indented(f, false)?;
                f.dedent(1);
                writeln!(f)?;
                write!(f, "}}")?;
                if newline_let {
                    f.dedent(1);
                }
                Ok(())
            }
            IrNode::Continue(c) => write!(f, "continue {c}",),
            IrNode::Var(i) => write!(f, "{i}"),
            IrNode::App(i, is) => write!(f, "{i} {}", fmt_args(is)),
            IrNode::Tuple(is) => write!(
                f,
                "({})",
                is.iter()
                    .map(|i| format!("{i}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            IrNode::Get(i, c) => write!(f, "{i}.({c})"),
            IrNode::Set(i, c, e) => write!(f, "{i}.({c}) <- {e}"),
            IrNode::ArrayMake(i1, i2) => write!(f, "Array.make {i1} {i2}"),
            IrNode::PrintInt(i) => write!(f, "print_int {i}"),
            IrNode::Pervasive(i, is) => write!(f, "{i} {}", fmt_args(is)),
        }
    }
}

impl<'a> IrNode<'a> {
    pub fn has_effect(&self) -> bool {
        match self {
            IrNode::If(IfExpr {
                clauses:
                    IfBranch::ThenElse {
                        then_: e1,
                        else_: e2,
                    },
                ..
            })
            | IrNode::Let(.., e1, e2) => e1.borrow().has_effect() || e2.borrow().has_effect(),
            IrNode::LetRec(.., e) | IrNode::LetTuple(.., e) => e.borrow().has_effect(),
            IrNode::App(..) | IrNode::Set(..) | IrNode::ArrayMake(..) | IrNode::PrintInt(..) => {
                true
            }
            IrNode::Pervasive(f, ..) => match V_ASM_PERVASIVES.get(f) {
                Some(info) => info.has_effect,
                None => true,
            },
            IrNode::Loop(..) | IrNode::Continue(Continue(..)) => true,
            _ => false,
        }
    }
}

impl<'b, 'a: 'b> IrNode<'a> {
    /// `IrNode` is invariant for `'a` because it internally uses `UnSafeCell`,
    /// but it is actually covariant
    pub fn cloned(&self) -> IrNode<'b> {
        fn rr<T>(v: T) -> Rc<RefCell<T>> {
            Rc::new(RefCell::new(v))
        }
        match self {
            Self::Const(arg0) => IrNode::Const(*arg0),
            Self::IUnOp(arg0, arg1) => IrNode::IUnOp(*arg0, arg1.clone()),
            Self::BBinOp(arg0, arg1, arg2) => IrNode::BBinOp(*arg0, arg1.clone(), arg2.clone()),
            Self::IBinOp(arg0, arg1, arg2) => IrNode::IBinOp(*arg0, arg1.clone(), arg2.clone()),
            Self::FUnOp(arg0, arg1) => IrNode::FUnOp(*arg0, arg1.clone()),
            Self::FBinOp(arg0, arg1, arg2) => IrNode::FBinOp(*arg0, arg1.clone(), arg2.clone()),
            Self::FTerOp(arg0, arg1, arg2, arg3) => {
                IrNode::FTerOp(*arg0, arg1.clone(), arg2.clone(), arg3.clone())
            }
            Self::If(IfExpr {
                cond,
                clauses: IfBranch::ThenElse { then_, else_ },
            }) => IrNode::If(IfExpr {
                cond: cond.clone(),
                clauses: IfBranch::ThenElse {
                    then_: rr(then_.borrow().cloned()),
                    else_: rr(else_.borrow().cloned()),
                },
            }),
            Self::Let(arg0, arg1, arg2) => IrNode::Let(
                arg0.clone(),
                rr(arg1.borrow().cloned()),
                rr(arg2.borrow().cloned()),
            ),
            Self::LetRec(FunDef { var, args, body }, arg1) => IrNode::LetRec(
                FunDef {
                    var: var.clone(),
                    args: args.clone(),
                    body: rr(body.borrow().cloned()),
                },
                rr(arg1.borrow().cloned()),
            ),
            Self::LetTuple(arg0, arg1, arg2) => {
                IrNode::LetTuple(arg0.clone(), arg1.clone(), rr(arg2.borrow().cloned()))
            }
            Self::Loop(arg0, arg1) => IrNode::Loop(arg0.clone(), rr(arg1.borrow().cloned())),
            Self::Continue(arg0) => IrNode::Continue(arg0.clone()),
            Self::Var(arg0) => IrNode::Var(arg0.clone()),
            Self::App(arg0, arg1) => IrNode::App(arg0.clone(), arg1.clone()),
            Self::Tuple(arg0) => IrNode::Tuple(arg0.clone()),
            Self::Get(arg0, arg1) => IrNode::Get(arg0.clone(), arg1.clone()),
            Self::Set(arg0, arg1, arg2) => IrNode::Set(arg0.clone(), arg1.clone(), arg2.clone()),
            Self::ArrayMake(arg0, arg1) => IrNode::ArrayMake(arg0.clone(), arg1.clone()),
            Self::PrintInt(arg0) => IrNode::PrintInt(arg0.clone()),
            Self::Pervasive(arg0, arg1) => IrNode::Pervasive(arg0, arg1.clone()),
        }
    }
}

impl<'a> Default for IrNode<'a> {
    fn default() -> Self {
        Self::Const(ConstKind::Unit)
    }
}

#[derive(Debug, Clone, Default)]
pub struct FunDef<'a> {
    pub var: VarDef<'a>,
    pub args: Vec<VarDef<'a>>,
    pub body: Rc<RefCell<IrNode<'a>>>,
}

impl<'a> FunDef<'a> {
    pub fn is_recursive(&self) -> bool {
        self.body.borrow().contains(&self.var)
    }
    pub fn contains_loop(&self) -> bool {
        self.body.borrow().contains_loop()
    }
    pub fn len(&self) -> usize {
        self.body.borrow().len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl IrNode<'_> {
    pub fn contains(&self, ident: &Ident) -> bool {
        use IrNode::*;
        use MaybeConst::*;
        match self {
            Const(_) => false,
            IUnOp(_, x) | FUnOp(_, x) | IBinOp(_, x, Constant(_)) => x == ident,
            Get(x, Constant(_)) | Var(x) => &x.name == ident,
            BBinOp(_, x, y) | IBinOp(_, x, Variable(y)) | FBinOp(_, x, y) => {
                x == ident || y == ident
            }
            FTerOp(_, x, y, z) => x == ident || y == ident || z == ident,
            Get(x, Variable(y)) | Set(x, Constant(_), VarDef { name: y, .. }) => {
                &x.name == ident || y == ident
            }
            If(IfExpr {
                cond,
                clauses: IfBranch::ThenElse { then_, else_ },
            }) => {
                (match cond {
                    IfCond::Bin { lhs, rhs, .. } => &lhs.name == ident || rhs == ident,
                    IfCond::Un { lhs, .. } => &lhs.name == ident,
                }) || then_.borrow().contains(ident)
                    || else_.borrow().contains(ident)
            }
            Let(VarDef { name, ty: _ }, e1, e2) => {
                name == ident || e1.borrow().contains(ident) || e2.borrow().contains(ident)
            }
            LetRec(fundef, e2) => {
                &fundef.var.name != ident
                    && (fundef.body.borrow().contains(ident) || e2.borrow().contains(ident))
            }
            App(x, ys) => x == ident || ys.iter().any(|y| &y.var.name == ident),
            Tuple(xs) => xs
                .iter()
                .filter_map(|x| match x {
                    Variable(x) => Some(x),
                    Constant(_) => None,
                })
                .any(|x| &x.name == ident),
            Pervasive(_, xs) => xs.iter().any(|x| &x.var.name == ident),
            LetTuple(xs, y, e) => {
                &y.name == ident
                    || (!xs.iter().any(|x| &x.name == ident) && e.borrow().contains(ident))
            }
            Loop(c, e) => c.contains(ident) || e.borrow().contains(ident),
            Continue(c) => c.contains(ident),
            Set(x, Variable(y), VarDef { name: z, .. }) => {
                &x.name == ident || y == ident || z == ident
            }
            ArrayMake(i1, i2) => [i1.as_ref(), i2.as_deref()]
                .iter()
                .filter_map(MaybeConst::as_variable)
                .cloned()
                .any(|x| x == ident),
            PrintInt(i) => i.as_variable().into_iter().any(|x| x == ident),
        }
    }
    pub fn contains_loop(&self) -> bool {
        use IrNode::*;
        match self {
            If(IfExpr {
                clauses: IfBranch::ThenElse { then_, else_ },
                ..
            }) => then_.borrow().contains_loop() || else_.borrow().contains_loop(),
            Let(.., e1, e2) => e1.borrow().contains_loop() || e2.borrow().contains_loop(),
            LetRec(fundef, e2) => {
                fundef.body.borrow().contains_loop() || e2.borrow().contains_loop()
            }
            LetTuple(.., e) => e.borrow().contains_loop(),
            Loop(..) => true,
            _ => false,
        }
    }
}

impl<'a> Continue<'a> {
    pub fn contains(&self, ident: &Ident) -> bool {
        self.1.iter().any(|(_, x)| &x.name == ident)
    }
}

#[derive(Default)]
pub struct PathState {
    modified: bool,
    used_var: HashMap<IdentSymbol, usize>,
    elim_static: HashMap<(IdentSymbol, i32), Option<ConstKind>>,
}

impl PathState {
    /// returns whether the node has room for further optimization
    pub fn modified(&self) -> bool {
        self.modified
    }
    pub fn clear_modified(&mut self) {
        self.modified = false;
    }
    pub(crate) fn did_modify(&mut self) {
        self.modified = true;
    }
    pub(crate) fn clear_usage(&mut self) {
        self.used_var.clear();
    }
    pub(crate) fn deprecate_var(&mut self, name: &IdentSymbol) {
        self.used_var.remove(name);
    }
    pub(crate) fn use_of_var(&mut self, name: &IdentSymbol) {
        self.used_var
            .entry(*name)
            .and_modify(|c| *c += 1)
            .or_insert(1);
    }
    pub(crate) fn is_unused(&self, name: &IdentSymbol) -> bool {
        !self.used_var.contains_key(name)
    }
    pub(crate) fn is_used_once(&self, name: &IdentSymbol) -> bool {
        self.used_var.get(name) == Some(&1)
    }
    pub(crate) fn can_elim_static(&mut self, name: IdentSymbol, index: i32) {
        self.elim_static.insert((name, index), None);
    }
    pub(crate) fn is_elim_static(&self, name: IdentSymbol, index: i32) -> bool {
        self.elim_static.contains_key(&(name, index))
    }
    pub(crate) fn get_elim_static_mut(
        &mut self,
        name: IdentSymbol,
        index: i32,
    ) -> Option<&mut Option<ConstKind>> {
        self.elim_static.get_mut(&(name, index))
    }
}
