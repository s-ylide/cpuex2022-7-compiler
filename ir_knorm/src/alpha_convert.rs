use std::{borrow::Cow, collections::HashMap, rc::Rc};

use typedefs::{Ident, IfBranch, IfCond, IfExpr};

use crate::{Continue, IrNode, VarDef};

#[derive(Debug)]
pub struct RenamingMap<'a, 'b> {
    inner: HashMap<Ident<'a>, Cow<'b, Ident<'a>>>,
    /// keep previously registered idents
    stashed: HashMap<Ident<'a>, Vec<Cow<'b, Ident<'a>>>>,
}

impl<'a, 'b> FromIterator<(Ident<'a>, &'b Ident<'a>)> for RenamingMap<'a, 'b> {
    fn from_iter<T: IntoIterator<Item = (Ident<'a>, &'b Ident<'a>)>>(iter: T) -> Self {
        Self {
            inner: iter
                .into_iter()
                .map(|(a, b)| (a, Cow::Borrowed(b)))
                .collect(),
            stashed: HashMap::new(),
        }
    }
}

impl<'a, 'b> FromIterator<(Ident<'a>, Ident<'a>)> for RenamingMap<'a, 'b> {
    fn from_iter<T: IntoIterator<Item = (Ident<'a>, Ident<'a>)>>(iter: T) -> Self {
        Self {
            inner: iter.into_iter().map(|(a, b)| (a, Cow::Owned(b))).collect(),
            stashed: HashMap::new(),
        }
    }
}

impl<'a, 'b> RenamingMap<'a, 'b> {
    fn new() -> Self {
        Self {
            inner: HashMap::new(),
            stashed: HashMap::new(),
        }
    }
    fn insert(&mut self, k: Ident<'a>, v: &'b Ident<'a>) {
        let old = self.inner.insert(k.clone(), Cow::Borrowed(v));
        if let Some(old) = old {
            self.stashed.entry(k).or_default().push(old);
        }
    }
    fn remove(&mut self, k: &Ident<'a>) {
        if let Some(stashed) = self.stashed.get_mut(k) {
            if let Some(back) = stashed.pop() {
                self.inner.insert(k.clone(), back);
            } else {
                self.inner.remove(k);
            }
        } else {
            self.inner.remove(k);
        }
    }
    fn rename(&self, ident: &'b mut Ident<'a>) {
        if let Some(renamed) = self.inner.get(ident) {
            *ident = renamed.clone().into_owned();
        }
    }
    fn make_unique(&mut self, ident: &'b mut Ident<'a>) {
        let cloned = ident.clone();
        ident.update();
        self.insert(cloned, ident);
    }
}

enum ModifyEnv<'a, 'b> {
    Bind(&'b mut Ident<'a>),
    BindMany(Vec<&'b mut Ident<'a>>),
    UnBind(Ident<'a>),
    UnBindMany(Vec<Ident<'a>>),
    Nop,
}

/// make all variable unique. binded variables are renamed.
/// unbinded variables (pervasives) remain unchanged.
pub fn alpha_convert(node: &mut IrNode) {
    let env = RenamingMap::new();
    alpha_convert_with_env(node, env)
}

pub fn alpha_convert_with_env<'a, 'b>(node: &'b mut IrNode<'a>, mut env: RenamingMap<'a, 'b>) {
    let mut stack: Vec<(Option<&mut IrNode>, ModifyEnv)> = Vec::new();
    use ModifyEnv::*;
    stack.push((Some(node), Nop));
    while let Some((node, m)) = stack.pop() {
        match m {
            Bind(rename) => {
                env.make_unique(rename);
            }
            BindMany(renames) => {
                for rename in renames {
                    env.make_unique(rename);
                }
            }
            UnBind(ident) => {
                env.remove(&ident);
            }
            UnBindMany(idents) => {
                for ident in idents {
                    env.remove(&ident);
                }
            }
            Nop => (),
        }
        if let Some(node) = node {
            match node {
                IrNode::Const(_) => (),
                IrNode::IUnOp(_, i) | IrNode::FUnOp(_, i) => {
                    env.rename(i);
                }
                IrNode::Var(i) => {
                    env.rename(i);
                }
                IrNode::BBinOp(_, i1, i2) | IrNode::FBinOp(_, i1, i2) => {
                    env.rename(i1);
                    env.rename(i2);
                }
                IrNode::FTerOp(_, i1, i2, i3) => {
                    env.rename(i1);
                    env.rename(i2);
                    env.rename(i3);
                }
                IrNode::IBinOp(_, i1, i2) => {
                    env.rename(i1);
                    if let Some(i2) = i2.as_variable_mut() {
                        env.rename(i2);
                    }
                }
                IrNode::If(IfExpr {
                    cond,
                    clauses: IfBranch::ThenElse { then_, else_ },
                }) => {
                    match cond {
                        IfCond::Bin { lhs, rhs, .. } => {
                            env.rename(lhs);
                            env.rename(rhs);
                        }
                        IfCond::Un { lhs, .. } => {
                            env.rename(lhs);
                        }
                    }
                    stack.push((Some(Rc::get_mut(else_).unwrap().get_mut()), Nop));
                    stack.push((Some(Rc::get_mut(then_).unwrap().get_mut()), Nop));
                }
                IrNode::Let(v, e1, e2) => {
                    let ident = v.name.clone();
                    stack.push((None, UnBind(ident)));
                    stack.push((Some(Rc::get_mut(e2).unwrap().get_mut()), Bind(&mut v.name)));
                    stack.push((Some(Rc::get_mut(e1).unwrap().get_mut()), Nop));
                }
                IrNode::LetRec(f, e) => {
                    let args: Vec<_> = f
                        .args
                        .iter_mut()
                        .map(|VarDef { name, ty: _ }| name)
                        .collect();
                    let args_ident = args.iter().map(|v| (*v).clone()).collect();
                    let ident = f.var.name.clone();
                    stack.push((None, UnBind(ident)));
                    stack.push((
                        Some(Rc::get_mut(e).unwrap().get_mut()),
                        UnBindMany(args_ident),
                    ));
                    stack.push((
                        Some(Rc::get_mut(&mut f.body).unwrap().get_mut()),
                        Bind(&mut f.var.name),
                    ));
                    stack.push((None, BindMany(args)));
                }
                IrNode::LetTuple(vs, i, e) => {
                    env.rename(i);
                    let bounds: Vec<_> = vs.iter_mut().map(|VarDef { name, ty: _ }| name).collect();
                    let names = bounds.iter().map(|v| (*v).clone()).collect();
                    stack.push((None, UnBindMany(names)));
                    stack.push((Some(Rc::get_mut(e).unwrap().get_mut()), BindMany(bounds)));
                }
                IrNode::Loop(Continue(l, is), e) => {
                    env.make_unique(l);
                    for (_, i) in is.iter_mut() {
                        env.rename(&mut i.name);
                    }
                    stack.push((
                        None,
                        UnBindMany(is.iter().map(|(p, _)| p.name.clone()).collect()),
                    ));
                    stack.push((
                        Some(Rc::get_mut(e).unwrap().get_mut()),
                        BindMany(is.iter_mut().map(|(p, _)| &mut p.name).collect()),
                    ));
                }
                IrNode::Continue(Continue(l, is)) => {
                    env.rename(l);
                    for (p, i) in is.iter_mut() {
                        env.rename(&mut p.name);
                        env.rename(&mut i.name);
                    }
                }
                IrNode::App(i, is) => {
                    is.retain(|v| !v.var.ty.as_concty().unwrap().is_unit());
                    env.rename(i);
                    for i in is.iter_mut() {
                        env.rename(&mut i.var.name);
                    }
                }
                IrNode::Tuple(is) => {
                    for i in is.iter_mut() {
                        if let Some(i) = i.as_variable_mut() {
                            env.rename(&mut i.name);
                        }
                    }
                }
                IrNode::Get(i1, i2) => {
                    env.rename(i1);
                    if let Some(i2) = i2.as_variable_mut() {
                        env.rename(i2);
                    }
                }
                IrNode::Set(i1, i2, i3) => {
                    env.rename(i1);
                    if let Some(i2) = i2.as_variable_mut() {
                        env.rename(i2);
                    }
                    env.rename(i3);
                }
                IrNode::ArrayMake(i1, i2) => {
                    if let Some(i1) = i1.as_variable_mut() {
                        env.rename(i1);
                    }
                    if let Some(i2) = i2.as_variable_mut() {
                        env.rename(i2);
                    }
                }
                IrNode::Pervasive(_, is) => {
                    is.retain(|v| !v.var.ty.as_concty().unwrap().is_unit());
                    for i in is.iter_mut() {
                        env.rename(&mut i.var.name);
                    }
                }
                IrNode::PrintInt(i) => {
                    if let Some(i) = i.as_variable_mut() {
                        env.rename(i);
                    }
                }
            }
        }
    }
}
