use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use ast::{BBinOpKind, ConstKind, FBinOpKind, FUnOpKind, IBinOpKind, IUnOpKind};
use pervasives::V_ASM_PERVASIVES;
use ty::ConcTy;
use typedefs::{Ident, IdentSymbol, IfBranch, IfExpr, MaybeConst, VarDef};
use util::union_find::UnionFind;

use crate::{Continue, IrNode, PathState};

struct IdentEquivs {
    inner: UnionFind<IdentSymbol, IdentEquivId>,
}

impl IdentEquivs {
    fn new() -> Self {
        Self {
            inner: UnionFind::new(),
        }
    }
    fn insert(&mut self, late: &IdentSymbol, early: &IdentSymbol) {
        let key1 = late;
        if self.inner.get_root_id(key1).is_none() {
            self.inner.make_set(*key1, IdentEquivId(*early));
        }
        let key2 = early;
        if self.inner.get_root_id(key2).is_none() {
            self.inner.make_set(*key2, IdentEquivId(*early));
        }
        self.inner.union(key1, key2).unwrap();
    }
    fn get_repr(&self, i: &IdentSymbol) -> IdentEquivId {
        self.inner.get_root_id(i).unwrap_or(IdentEquivId(*i))
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
struct IdentEquivId(IdentSymbol);

#[derive(PartialEq, Eq, Hash)]
enum ExprId<'a> {
    Const(ConstKind),
    IUnOp(IUnOpKind, IdentEquivId),
    BBinOp(BBinOpKind, IdentEquivId, IdentEquivId),
    IBinOp(IBinOpKind, IdentEquivId, IdOrConst),
    FUnOp(FUnOpKind, IdentEquivId),
    FBinOp(FBinOpKind, IdentEquivId, IdentEquivId),
    Tuple(Vec<IdOrConst>),
    Pervasive(ast::Ident<'a>, Vec<IdentEquivId>),
}

#[derive(PartialEq, Eq, Hash)]
enum IdOrConst {
    C(ConstKind),
    Id(IdentEquivId),
}

type CachedVar<'a> = HashMap<ConcTy, HashMap<i32, HashMap<IdentSymbol, VarDef<'a>>>>;

/// find and eliminate common subexpression.
/// do not call before flatten let.
pub fn elim_common_expr(node: &mut IrNode, st: &mut PathState) {
    let mut ie = IdentEquivs::new();
    let mut defined_var_map: HashMap<ExprId, VarDef> = HashMap::new();
    let mut unbinded: HashSet<&IdentSymbol> = HashSet::new();
    enum ModifyEnv<'a, 'b> {
        Node(&'b mut IrNode<'a>),
        Unbind(&'b IdentSymbol),
        Restore(CachedVar<'a>),
        Reset,
    }
    use ModifyEnv::*;
    let mut stack: Vec<ModifyEnv> = vec![Node(node)];
    let mut cache: CachedVar = HashMap::new();
    // when pointer escapes, alias become unchaseable
    let mut escaped: HashSet<IdentSymbol> = HashSet::new();

    fn mu<T>(r: &mut Rc<RefCell<T>>) -> &mut T {
        Rc::get_mut(r).unwrap().get_mut()
    }

    use IdOrConst::*;
    use MaybeConst::*;
    while let Some(node) = stack.pop() {
        match node {
            Reset => {
                cache.clear();
            }
            Restore(a) => {
                cache = a;
            }
            Node(node) => {
                enum Concern<'a> {
                    Beta(IdentSymbol),
                    Get(IdentSymbol, i32, ConcTy),
                    OtherExpr(ExprId<'a>),
                    /// cancel replacing this expression
                    Cancel,
                }
                use Concern::*;
                fn get_expr_id<'a>(
                    cache: &mut CachedVar<'a>,
                    escaped: &mut HashSet<IdentSymbol>,
                    ie: &IdentEquivs,
                    this_bind: Option<&VarDef<'a>>,
                    node: &IrNode<'a>,
                ) -> Concern<'a> {
                    use ExprId::*;
                    OtherExpr(match node {
                        IrNode::Const(ConstKind::Unit) => return Cancel,
                        IrNode::Const(c) => Const(*c),
                        IrNode::IUnOp(k, i) => IUnOp(*k, ie.get_repr(i)),
                        IrNode::BBinOp(k, i1, i2) => BBinOp(*k, ie.get_repr(i1), ie.get_repr(i2)),
                        IrNode::IBinOp(k, i, Constant(c)) => IBinOp(*k, ie.get_repr(i), C(*c)),
                        IrNode::IBinOp(k, i1, Variable(i2)) => {
                            IBinOp(*k, ie.get_repr(i1), Id(ie.get_repr(i2)))
                        }
                        IrNode::FUnOp(k, i) => FUnOp(*k, ie.get_repr(i)),
                        IrNode::FBinOp(k, i1, i2) => FBinOp(*k, ie.get_repr(i1), ie.get_repr(i2)),
                        IrNode::Var(i) => {
                            // beta convert must remove this possibility
                            escaped.insert(*i.id());
                            if let Some(v) = this_bind {
                                escaped.insert(*v.id());
                            }
                            return Beta(*i.id());
                        }
                        IrNode::App(.., is) => {
                            escaped.extend(is.iter().map(|v| v.id()));
                            cache.clear();
                            return Cancel;
                        }
                        IrNode::Tuple(is) => {
                            let mut v = Vec::new();
                            for i in is {
                                v.push(match i {
                                    Variable(i) => {
                                        escaped.insert(*i.id());
                                        Id(ie.get_repr(i))
                                    }
                                    Constant(c) => C(*c),
                                });
                            }
                            if let Some(v) = this_bind {
                                for (i, cc) in is.iter().enumerate() {
                                    if let Some(elm) = cc.as_variable() {
                                        let ty = elm.ty.as_concty().unwrap();
                                        cache
                                            .entry(ty)
                                            .or_default()
                                            .entry(i as i32)
                                            .or_default()
                                            .insert(*v.id(), elm.to_owned());
                                    }
                                }
                            }
                            Tuple(v)
                        }
                        IrNode::Get(a, Constant(idx)) => {
                            let idx = *idx.as_int().unwrap();
                            let ty = a.ty.as_concty().unwrap().as_nth(idx as usize).unwrap();
                            return Get(*a.id(), idx, ty);
                        }
                        IrNode::Set(a, idx, rhs) => {
                            match idx {
                                MaybeConst::Variable(_) => {
                                    cache
                                        .entry(rhs.ty.as_concty().unwrap())
                                        .and_modify(|ty| ty.clear());
                                    return Cancel;
                                }
                                MaybeConst::Constant(i) => {
                                    let idx = *i.as_int().unwrap();
                                    let t = rhs.ty.as_concty().unwrap();
                                    if !escaped.contains(a.id()) {
                                        cache
                                            .entry(t)
                                            .or_default()
                                            .entry(idx)
                                            .and_modify(|m| m.clear())
                                            .or_default()
                                            .insert(*a.id(), rhs.to_owned());
                                    } else {
                                        cache.entry(t).and_modify(|m| m.clear());
                                    }
                                    return Cancel;
                                }
                            };
                        }
                        IrNode::ArrayMake(_, Variable(i)) => {
                            escaped.insert(*i.id());
                            return Cancel;
                        }
                        IrNode::Pervasive(f, is)
                            if !V_ASM_PERVASIVES.get(f).unwrap().has_effect =>
                        {
                            let mut v = Vec::new();
                            for i in is {
                                v.push(ie.get_repr(i));
                            }
                            Pervasive(f, v)
                        }
                        IrNode::If(_)
                        | IrNode::Let(_, _, _)
                        | IrNode::LetRec(_, _)
                        | IrNode::LetTuple(_, _, _) => unreachable!(),
                        _ => return Cancel,
                    })
                }

                #[allow(clippy::too_many_arguments)]
                fn replace_if_possible<'a>(
                    c: Concern<'a>,
                    unbinded: &HashSet<&IdentSymbol>,
                    ie: &mut IdentEquivs,
                    this_bind: Option<&mut VarDef<'a>>,
                    defined_var_map: &mut HashMap<ExprId<'a>, VarDef<'a>>,
                    node: &mut IrNode<'a>,
                    st: &mut PathState,
                    escaped: &HashSet<IdentSymbol>,
                    cache: &mut CachedVar<'a>,
                ) {
                    match c {
                        Beta(var) => {
                            if !unbinded.contains(&var) {
                                if let Some(this_bind) = this_bind {
                                    ie.insert(this_bind, &var);
                                }
                            }
                        }
                        OtherExpr(eid) => {
                            // the same expression is already defined
                            match defined_var_map.get(&eid) {
                                Some(var) if !unbinded.contains(var.id()) => {
                                    if let Some(this_bind) = this_bind {
                                        ie.insert(this_bind, var);
                                    }
                                    *node = IrNode::Var((*var).to_owned());
                                    st.did_modify();
                                }
                                _ => {
                                    if let Some(this_bind) = this_bind {
                                        defined_var_map.insert(eid, this_bind.to_owned());
                                    }
                                }
                            }
                        }
                        Get(a, i, t) => {
                            if !escaped.contains(&a) {
                                match cache
                                    .get(&t)
                                    .and_then(|m| m.get(&i))
                                    .and_then(|m| m.get(&a))
                                {
                                    Some(var) if !unbinded.contains(var.id()) => {
                                        // dbg!(&node, var);
                                        *node = IrNode::Var(var.to_owned());
                                        st.did_modify();
                                    }
                                    _ => {
                                        if let Some(this_bind) = this_bind {
                                            cache
                                                .entry(t)
                                                .or_default()
                                                .entry(i)
                                                .or_default()
                                                .insert(a, this_bind.to_owned());
                                        }
                                    }
                                }
                            }
                        }
                        Cancel => (),
                    }
                }

                match node {
                    IrNode::Let(v, e1, e2) => {
                        let e = mu(e1);
                        match e {
                            IrNode::Loop(..)
                            | IrNode::Let(..)
                            | IrNode::LetRec(..)
                            | IrNode::If(..) => {
                                stack.push(Unbind(v));
                                stack.push(Node(mu(e2)));
                                stack.push(Node(e));
                            }
                            _ => {
                                let c = get_expr_id(&mut cache, &mut escaped, &ie, Some(v), e);
                                replace_if_possible(
                                    c,
                                    &unbinded,
                                    &mut ie,
                                    Some(v),
                                    &mut defined_var_map,
                                    e,
                                    st,
                                    &escaped,
                                    &mut cache,
                                );
                                stack.push(Unbind(v));
                                stack.push(Node(mu(e2)));
                            }
                        }
                    }
                    IrNode::If(IfExpr {
                        clauses:
                            IfBranch::ThenElse {
                                then_: e1,
                                else_: e2,
                            },
                        ..
                    }) => {
                        stack.push(Reset);
                        stack.push(Node(mu(e2)));
                        stack.push(Restore(cache.clone()));
                        stack.push(Node(mu(e1)));
                    }
                    IrNode::LetRec(def, e) => {
                        let body = &mut def.body;
                        stack.push(Node(mu(e)));
                        // enter with new environment
                        elim_common_expr(mu(body), st);
                    }
                    IrNode::Continue(Continue(.., args)) => {
                        cache.clear();
                        escaped.extend(args.iter().map(|(_, a)| *a.id()));
                    }
                    IrNode::Loop(Continue(l, args), e) => {
                        let AliasEscapeEffect { escape, .. } = collect_loop_effect(&e.borrow(), l);
                        escaped.extend(escape.0);
                        escaped.extend(args.iter().map(|(_, a)| *a.id()));
                        stack.push(Reset);
                        stack.push(Node(mu(e)));
                        stack.push(Reset);
                    }
                    // other expression have an opportunity of CSE
                    e => {
                        let c = get_expr_id(&mut cache, &mut escaped, &ie, None, e);
                        replace_if_possible(
                            c,
                            &unbinded,
                            &mut ie,
                            None,
                            &mut defined_var_map,
                            e,
                            st,
                            &escaped,
                            &mut cache,
                        );
                    }
                }
            }
            Unbind(v) => {
                unbinded.insert(v);
            }
        }
    }
}

enum AliasModification {
    Remove(Vec<ConcTy>),
    Clear,
}

impl AliasModification {
    fn new() -> Self {
        Self::Remove(Vec::new())
    }
    fn merge(&mut self, other: Self) {
        match (self, other) {
            (Self::Remove(v1), Self::Remove(mut v2)) => {
                v1.append(&mut v2);
            }
            (Self::Clear, _) => (),
            (s, Self::Clear) => {
                *s = Self::Clear;
            }
        }
    }
    fn remove(&mut self, k: ConcTy) {
        match self {
            AliasModification::Remove(s) => s.push(k),
            AliasModification::Clear => (),
        }
    }
    fn clear(&mut self) {
        *self = Self::Clear;
    }
}

impl Default for AliasModification {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Default)]
struct EscapeIdents(Vec<IdentSymbol>);

impl EscapeIdents {
    fn merge(&mut self, mut other: Self) {
        self.0.append(&mut other.0);
    }
}

#[derive(Default)]
struct AliasEscapeEffect {
    alias: AliasModification,
    escape: EscapeIdents,
}

impl AliasEscapeEffect {
    fn merge(&mut self, other: Self) {
        self.alias.merge(other.alias);
        self.escape.merge(other.escape);
    }
    fn merged(mut self, other: Self) -> Self {
        self.merge(other);
        self
    }
}

/// collect effect
fn collect_loop_effect<'a>(node: &IrNode<'a>, label: &Ident<'a>) -> AliasEscapeEffect {
    let mut effects = AliasEscapeEffect::default();
    enum RefTrv<'a, 'b> {
        Node(Rc<RefCell<IrNode<'a>>>),
        Root(&'b IrNode<'a>),
        End,
    }
    use RefTrv::*;
    let mut stack = vec![Root(node)];
    while let Some(t) = stack.pop() {
        match t {
            Node(r) => visit_node(&r.borrow(), &mut stack, &mut effects, label),
            Root(r) => visit_node(r, &mut stack, &mut effects, label),
            End => return effects,
        }
        fn visit_node<'a>(
            node: &IrNode<'a>,
            stack: &mut Vec<RefTrv<'a, '_>>,
            effects: &mut AliasEscapeEffect,
            label: &Ident<'a>,
        ) {
            use MaybeConst::*;
            fn mu<'a, 'b>(r: &Rc<RefCell<IrNode<'a>>>) -> RefTrv<'a, 'b> {
                Node(r.clone())
            }
            match node {
                IrNode::Let(_, e1, e2) => {
                    stack.push(mu(e2));
                    stack.push(mu(e1));
                }
                IrNode::LetRec(_, e) => {
                    stack.push(mu(e));
                }
                IrNode::If(IfExpr {
                    clauses: IfBranch::ThenElse { then_, else_ },
                    ..
                }) => effects.merge(
                    collect_loop_effect(&then_.borrow(), label)
                        .merged(collect_loop_effect(&else_.borrow(), label)),
                ),
                IrNode::Var(i) => {
                    effects.escape.0.push(*i.id());
                    effects.alias.remove(i.ty.as_concty().unwrap());
                }
                IrNode::App(_, is) => {
                    effects.escape.0.extend(is.iter().map(|v| v.id()));
                    effects.alias.clear();
                }
                IrNode::Tuple(is) => {
                    for i in is {
                        if let Variable(i) = i {
                            effects.escape.0.push(*i.id());
                        }
                    }
                }
                IrNode::Set(.., rhs) => {
                    effects.alias.remove(rhs.ty.as_concty().unwrap());
                }
                IrNode::ArrayMake(_, Variable(i)) => {
                    effects.escape.0.push(*i.id());
                }
                IrNode::Loop(Continue(label, ..), b) => {
                    effects.merge(collect_loop_effect(&b.borrow(), label))
                }
                IrNode::Continue(Continue(l, ..)) => {
                    if l == label {
                        stack.push(End);
                    }
                }
                _ => (),
            }
        }
    }
    AliasEscapeEffect::default()
}
