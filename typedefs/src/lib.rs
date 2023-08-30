use std::{
    borrow,
    fmt::{self, Display},
    hash::Hash,
    ops::{self, Deref},
    sync::atomic::{AtomicUsize, Ordering},
};

use ast::{ConstKind, FUnOpKind};
use ty::{ConcTy, Ty};

#[derive(Debug, Clone)]
pub enum Ident<'a> {
    Source(ast::Ident<'a>),
    UniquelyNamed(String, IdentSymbol),
    Named(String, IdentSymbol),
    AlphaConverted(ast::Ident<'a>, IdentSymbol),
    Temporal(IdentSymbol),
}

impl Hash for Ident<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Source(a) => a.hash(state),
            s => s.id().hash(state),
        }
    }
}

impl PartialEq for Ident<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Source(l0), Self::Source(r0)) => l0 == r0,
            (Self::Source(_), _) | (_, Self::Source(_)) => false,
            (l, r) => l.id() == r.id(),
        }
    }
}

impl Eq for Ident<'_> {}

impl<'a> borrow::Borrow<IdentSymbol> for Ident<'a> {
    fn borrow(&self) -> &IdentSymbol {
        self
    }
}

impl<'a> ops::Deref for Ident<'a> {
    type Target = IdentSymbol;

    fn deref(&self) -> &Self::Target {
        self.id()
    }
}

impl<'a> Ident<'a> {
    pub fn id(&self) -> &IdentSymbol {
        match self {
            Ident::UniquelyNamed(_, s) => s,
            Ident::Named(_, s) => s,
            Ident::AlphaConverted(_, s) => s,
            Ident::Temporal(s) => s,
            Ident::Source(_) => panic!("do not call this method"),
        }
    }
    pub fn new() -> Self {
        Self::Temporal(IdentSymbol::new())
    }
    pub fn uniq_name(name: impl Into<String>) -> Self {
        Self::UniquelyNamed(name.into(), IdentSymbol::new())
    }
    pub fn ubiq_name(name: impl Into<String>) -> Self {
        Self::Named(name.into(), IdentSymbol::new())
    }
    pub fn updated(&self) -> Self {
        let mut s = self.clone();
        s.update();
        s
    }
    pub fn update(&mut self) {
        match self {
            Self::Source(s) => *self = Ident::AlphaConverted(s, IdentSymbol::new()),
            Self::UniquelyNamed(_, symbol)
            | Self::Named(_, symbol)
            | Self::AlphaConverted(_, symbol)
            | Self::Temporal(symbol) => symbol.update(),
        }
    }
    pub fn as_source(&self) -> Option<ast::Ident<'a>> {
        match self {
            Ident::Source(s) => Some(s),
            _ => None,
        }
    }
    pub fn to_unique_string(&self) -> String {
        match self {
            Ident::Source(s) => s.to_string(),
            Ident::UniquelyNamed(s, id) => format!("{s}${id}"),
            Ident::Named(s, id) => format!("{s}${id}"),
            Ident::AlphaConverted(s, id) => format!("{s}${id}"),
            Ident::Temporal(id) => format!("tmp{id}"),
        }
    }
    pub fn to_inner_string(&self) -> String {
        match self {
            Ident::Source(s) | Ident::AlphaConverted(s, _) => s.to_string(),
            Ident::UniquelyNamed(s, _) | Ident::Named(s, _) => s.to_owned(),
            Ident::Temporal(id) => format!("tmp{id}"),
        }
    }
}

impl Default for Ident<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl Display for Ident<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ident::Source(s) => f.write_str(s),
            Ident::UniquelyNamed(s, _) => write!(f, "{s}"),
            Ident::Named(s, id) => write!(f, "{s}${id}"),
            Ident::AlphaConverted(s, id) => write!(f, "{s}${id}"),
            Ident::Temporal(id) => write!(f, "__tmp{id}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct IdentSymbol(usize);

impl IdentSymbol {
    pub fn new() -> Self {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        Self(COUNTER.fetch_add(1, Ordering::SeqCst))
    }
    pub fn inner(&self) -> usize {
        self.0
    }
    pub fn update(&mut self) {
        *self = Self::new();
    }
}

impl Default for IdentSymbol {
    fn default() -> Self {
        Self::new()
    }
}

impl Display for IdentSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:02}", self.0)
    }
}

#[derive(Debug, Clone)]
pub enum Label<'a> {
    Ident(Ident<'a>),
    Named(String, IdentSymbol),
    RawNamed(String),
    Unique(String, IdentSymbol),
    Temporal(IdentSymbol),
}

impl Hash for Label<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::RawNamed(a) => a.hash(state),
            s => s.id().hash(state),
        }
    }
}

impl PartialEq for Label<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::RawNamed(l0), Self::RawNamed(r0)) => l0 == r0,
            (Self::RawNamed(_), _) | (_, Self::RawNamed(_)) => false,
            (l, r) => l.id() == r.id(),
        }
    }
}

impl Eq for Label<'_> {}

impl<'a> borrow::Borrow<IdentSymbol> for Label<'a> {
    fn borrow(&self) -> &IdentSymbol {
        self
    }
}

impl<'a> ops::Deref for Label<'a> {
    type Target = IdentSymbol;

    fn deref(&self) -> &Self::Target {
        self.id()
    }
}

impl<'a> Label<'a> {
    pub fn id(&self) -> &IdentSymbol {
        match self {
            Label::Ident(i) => i.id(),
            Label::Named(_, s) => s,
            Label::Unique(_, s) => s,
            Label::Temporal(s) => s,
            Label::RawNamed(_) => panic!("do not call this method"),
        }
    }
}

impl<'a> From<Ident<'a>> for Label<'a> {
    fn from(v: Ident<'a>) -> Self {
        Self::Ident(v)
    }
}

impl Display for Label<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Label::Ident(id) => write!(f, "{id}"),
            Label::Named(s, t) => write!(f, "{s}.{t}"),
            Label::RawNamed(s) => write!(f, "{s}"),
            Label::Unique(s, _) => write!(f, "{s}"),
            Label::Temporal(t) => write!(f, "l{t}"),
        }
    }
}

impl<'a> Label<'a> {
    pub fn new() -> Self {
        Self::Temporal(IdentSymbol::new())
    }
    pub fn raw_name(name: impl Into<String>) -> Self {
        Self::RawNamed(name.into())
    }
    pub fn name(name: impl Into<String>) -> Self {
        Self::Named(name.into(), IdentSymbol::new())
    }
    pub fn uniq_name(name: impl Into<String>) -> Self {
        Self::Unique(name.into(), IdentSymbol::new())
    }

    pub fn as_ident(&self) -> Option<&Ident<'a>> {
        if let Self::Ident(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn to_unique_string(&self) -> String {
        match self {
            Label::Ident(id) => id.to_unique_string(),
            Label::Named(s, t) => format!("{s}.{t}"),
            Label::RawNamed(s) => s.to_string(),
            Label::Unique(s, t) => format!("{s}.{t}"),
            Label::Temporal(t) => format!("l{t}"),
        }
    }
    pub fn to_inner_string(&self) -> String {
        match self {
            Label::Ident(id) => id.to_inner_string(),
            Label::Named(s, _) | Label::RawNamed(s) | Label::Unique(s, _) => s.to_owned(),
            Label::Temporal(_) => panic!("do not call with temporal"),
        }
    }
}

impl Default for Label<'_> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Default)]
pub struct VarDef<'a> {
    pub name: Ident<'a>,
    pub ty: Ty,
}

impl<'a> std::ops::DerefMut for VarDef<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.name
    }
}

impl<'a> std::ops::Deref for VarDef<'a> {
    type Target = Ident<'a>;

    fn deref(&self) -> &Self::Target {
        &self.name
    }
}

impl<'a> Display for VarDef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl<'a> From<ast::VarDef<'a>> for VarDef<'a> {
    fn from(ast::VarDef { name, ty }: ast::VarDef<'a>) -> Self {
        Self {
            name: Ident::Source(name),
            ty,
        }
    }
}

#[derive(Debug, Clone)]
pub enum MaybeConst<Ident> {
    Variable(Ident),
    Constant(ConstKind),
}

impl<Ident> MaybeConst<Ident> {
    pub fn as_ref(&self) -> MaybeConst<&Ident> {
        use MaybeConst::*;
        match self {
            Variable(v) => Variable(v),
            Constant(c) => Constant(*c),
        }
    }
}

impl<Ident: Deref> MaybeConst<Ident> {
    pub fn as_deref(&self) -> MaybeConst<&Ident::Target> {
        use MaybeConst::*;
        match self {
            Variable(v) => Variable(v),
            Constant(c) => Constant(*c),
        }
    }
}

impl<Ident> Default for MaybeConst<Ident> {
    fn default() -> Self {
        Self::Constant(Default::default())
    }
}

impl<T: Display> Display for MaybeConst<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeConst::Variable(i) => write!(f, "{i}"),
            MaybeConst::Constant(c) => write!(f, "{c}"),
        }
    }
}

impl<T> MaybeConst<T> {
    pub fn as_variable_mut(&mut self) -> Option<&mut T> {
        if let Self::Variable(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_variable(&self) -> Option<&T> {
        if let Self::Variable(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl<'a> MaybeConst<VarDef<'a>> {
    pub fn get_concty(&self) -> ConcTy {
        match self {
            MaybeConst::Variable(d) => d.ty.as_concty().unwrap(),
            MaybeConst::Constant(c) => c.get_concty(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct CanbeConst<Ident> {
    pub var: Ident,
    pub value: Option<ConstKind>,
}

impl<Ident: Deref> Deref for CanbeConst<Ident> {
    type Target = Ident;

    fn deref(&self) -> &Self::Target {
        &self.var
    }
}

impl<Ident> CanbeConst<Ident> {
    pub fn new(var: Ident) -> Self {
        Self { var, value: None }
    }
}

impl<T: Display> Display for CanbeConst<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            Some(v) => write!(f, "{}[ = {}]", self.var, v),
            None => write!(f, "{}", self.var),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum IfBinKind {
    I(IfBinIKind),
    F(IfBinFKind),
}

impl IfBinKind {
    pub fn fix_rhs_z(&self) -> IfUnKind {
        match self {
            IfBinKind::I(i) => IfUnKind::I(match i {
                IfBinIKind::Eq => IfUnIKind::Eqz,
                IfBinIKind::Le => IfUnIKind::Lez,
                IfBinIKind::Ge => IfUnIKind::Gez,
                IfBinIKind::Ne => IfUnIKind::Nez,
                IfBinIKind::Lt => IfUnIKind::Ltz,
                IfBinIKind::Gt => IfUnIKind::Gtz,
                IfBinIKind::Xor => IfUnIKind::Nez,
                IfBinIKind::Xnor => IfUnIKind::Eqz,
            }),
            IfBinKind::F(f) => IfUnKind::F(match f {
                IfBinFKind::Flt => IfUnFKind::Fltz,
                IfBinFKind::Fge => IfUnFKind::Fgez,
            }),
        }
    }
    pub fn fix_lhs_z(&self) -> IfUnKind {
        match self {
            IfBinKind::I(i) => IfUnKind::I(match i {
                IfBinIKind::Eq => IfUnIKind::Eqz,
                IfBinIKind::Le => IfUnIKind::Gez,
                IfBinIKind::Ge => IfUnIKind::Lez,
                IfBinIKind::Ne => IfUnIKind::Nez,
                IfBinIKind::Lt => IfUnIKind::Gtz,
                IfBinIKind::Gt => IfUnIKind::Ltz,
                IfBinIKind::Xor => IfUnIKind::Nez,
                IfBinIKind::Xnor => IfUnIKind::Eqz,
            }),
            IfBinKind::F(f) => IfUnKind::F(match f {
                IfBinFKind::Flt => IfUnFKind::Fgtz,
                IfBinFKind::Fge => IfUnFKind::Flez,
            }),
        }
    }
    pub fn try_into_i(self) -> Result<IfBinIKind, Self> {
        if let Self::I(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    pub fn try_into_f(self) -> Result<IfBinFKind, Self> {
        if let Self::F(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }
    pub fn symbol(&self) -> &'static str {
        match self {
            IfBinKind::I(s) => s.symbol(),
            IfBinKind::F(s) => s.symbol(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum IfBinFKind {
    Flt,
    Fge,
}

impl IfBinFKind {
    pub fn eval(&self, lhs: f32, rhs: f32) -> bool {
        match self {
            IfBinFKind::Flt => lhs < rhs,
            IfBinFKind::Fge => lhs >= rhs,
        }
    }
    pub fn symbol(&self) -> &'static str {
        match self {
            IfBinFKind::Flt => "<",
            IfBinFKind::Fge => ">=",
        }
    }
    pub fn negated(&self) -> Self {
        match self {
            IfBinFKind::Flt => IfBinFKind::Fge,
            IfBinFKind::Fge => IfBinFKind::Flt,
        }
    }
}

impl From<ast::BBinOpKind> for IfBinIKind {
    fn from(value: ast::BBinOpKind) -> Self {
        match value {
            ast::BBinOpKind::Eq => Self::Eq,
            ast::BBinOpKind::Le => Self::Le,
            ast::BBinOpKind::Ge => Self::Ge,
            ast::BBinOpKind::Ne => Self::Ne,
            ast::BBinOpKind::Lt => Self::Lt,
            ast::BBinOpKind::Gt => Self::Gt,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IfBinIKind {
    Eq,
    Le,
    Ge,
    Ne,
    Lt,
    Gt,
    Xor,
    Xnor,
}

impl IfBinIKind {
    pub fn eval(&self, lhs: i32, rhs: i32) -> bool {
        match self {
            Self::Eq => lhs == rhs,
            Self::Le => lhs <= rhs,
            Self::Ge => lhs >= rhs,
            Self::Ne => lhs != rhs,
            Self::Lt => lhs < rhs,
            Self::Gt => lhs > rhs,
            Self::Xor => lhs ^ rhs != 0,
            Self::Xnor => lhs ^ rhs == 0,
        }
    }
    pub fn symbol(&self) -> &'static str {
        match self {
            Self::Eq => "==",
            Self::Le => "<=",
            Self::Ge => ">=",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::Xor => "^",
            Self::Xnor => "xnor",
        }
    }
    pub fn negated(&self) -> Self {
        match self {
            Self::Eq => Self::Ne,
            Self::Le => Self::Gt,
            Self::Ge => Self::Lt,
            Self::Ne => Self::Eq,
            Self::Lt => Self::Ge,
            Self::Gt => Self::Le,
            Self::Xor => Self::Xnor,
            Self::Xnor => Self::Xor,
        }
    }
    pub fn flipped_arg(&self) -> Self {
        match self {
            Self::Eq => Self::Eq,
            Self::Le => Self::Ge,
            Self::Ge => Self::Le,
            Self::Ne => Self::Ne,
            Self::Lt => Self::Gt,
            Self::Gt => Self::Lt,
            Self::Xor => Self::Xor,
            Self::Xnor => Self::Xnor,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum IfUnKind {
    I(IfUnIKind),
    F(IfUnFKind),
}

impl IfUnKind {
    pub fn try_into_i(self) -> Result<IfUnIKind, Self> {
        if let Self::I(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }

    pub fn try_into_f(self) -> Result<IfUnFKind, Self> {
        if let Self::F(v) = self {
            Ok(v)
        } else {
            Err(self)
        }
    }
    pub fn symbol(&self) -> &'static str {
        match self {
            IfUnKind::I(s) => s.symbol(),
            IfUnKind::F(s) => s.symbol(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum IfUnIKind {
    Eqz,
    Lez,
    Gez,
    Nez,
    Ltz,
    Gtz,
}

impl IfUnIKind {
    pub fn eval(&self, i: i32) -> bool {
        match self {
            IfUnIKind::Eqz => i == 0,
            IfUnIKind::Lez => i <= 0,
            IfUnIKind::Gez => i >= 0,
            IfUnIKind::Nez => i != 0,
            IfUnIKind::Ltz => i < 0,
            IfUnIKind::Gtz => i > 0,
        }
    }
    pub fn symbol(&self) -> &'static str {
        match self {
            IfUnIKind::Eqz => "==",
            IfUnIKind::Lez => "<=",
            IfUnIKind::Gez => ">=",
            IfUnIKind::Nez => "!=",
            IfUnIKind::Ltz => "<",
            IfUnIKind::Gtz => ">",
        }
    }
    pub fn negated(&self) -> Self {
        match self {
            IfUnIKind::Eqz => IfUnIKind::Nez,
            IfUnIKind::Lez => IfUnIKind::Gtz,
            IfUnIKind::Gez => IfUnIKind::Ltz,
            IfUnIKind::Nez => IfUnIKind::Eqz,
            IfUnIKind::Ltz => IfUnIKind::Gez,
            IfUnIKind::Gtz => IfUnIKind::Lez,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum IfUnFKind {
    Fgtz,
    Fltz,
    Feqz,
    Fnez,
    Flez,
    Fgez,
}

impl TryFrom<FUnOpKind> for IfUnFKind {
    type Error = ();

    fn try_from(value: FUnOpKind) -> Result<Self, Self::Error> {
        match value {
            FUnOpKind::Fiszero => Ok(Self::Feqz),
            FUnOpKind::Fispos => Ok(Self::Fgtz),
            FUnOpKind::Fisneg => Ok(Self::Fltz),
            _ => Err(()),
        }
    }
}

impl IfUnFKind {
    pub fn eval(&self, f: f32) -> bool {
        match self {
            IfUnFKind::Feqz => f == 0.0,
            IfUnFKind::Fgtz => f > 0.0,
            IfUnFKind::Fltz => f < 0.0,
            IfUnFKind::Fnez => f != 0.0,
            IfUnFKind::Flez => f <= 0.0,
            IfUnFKind::Fgez => f >= 0.0,
        }
    }
    pub fn symbol(&self) -> &'static str {
        match self {
            IfUnFKind::Fgtz => ">",
            IfUnFKind::Fltz => "<",
            IfUnFKind::Feqz => "==",
            IfUnFKind::Fnez => "!=",
            IfUnFKind::Flez => "<=",
            IfUnFKind::Fgez => ">=",
        }
    }
    pub fn negated(&self) -> Self {
        match self {
            IfUnFKind::Fgtz => IfUnFKind::Flez,
            IfUnFKind::Fltz => IfUnFKind::Fgez,
            IfUnFKind::Feqz => IfUnFKind::Fnez,
            IfUnFKind::Fnez => IfUnFKind::Feqz,
            IfUnFKind::Flez => IfUnFKind::Fgtz,
            IfUnFKind::Fgez => IfUnFKind::Fltz,
        }
    }
}

#[derive(Debug, Clone)]
pub struct IfExpr<WithType, Ident, Body> {
    pub cond: IfCond<WithType, Ident>,
    pub clauses: IfBranch<Body>,
}

#[derive(Debug, Clone)]
pub enum IfCond<WithType, Ident> {
    Bin {
        op: IfBinKind,
        lhs: WithType,
        rhs: Ident,
    },
    Un {
        op: IfUnKind,
        lhs: WithType,
    },
}

impl<WithType: fmt::Display, Ident: fmt::Display> fmt::Display for IfCond<WithType, Ident> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IfCond::Bin { op, lhs, rhs } => write!(f, "{lhs} {op} {rhs}", op = op.symbol()),
            IfCond::Un { op, lhs } => write!(f, "{lhs} {op} 0", op = op.symbol()),
        }
    }
}

#[derive(Debug, Clone)]
pub enum IfBranch<Body> {
    ThenElse { then_: Body, else_: Body },
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    #[test]
    fn test_borrow_hm() {
        let mut m = HashMap::new();
        let ident = Ident::new();
        let id = *ident.id();
        m.insert(ident.clone(), 0);
        assert_eq!(m.get(&ident), Some(&0));
        assert_eq!(m.get(&id), Some(&0));
    }
}
