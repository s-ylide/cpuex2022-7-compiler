use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
    fmt::{self, Display},
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

use util::union_find::{UnionFind, UnionResult};

#[derive(Debug, Clone, Eq)]
pub enum ConcTy {
    Unit,
    Bool,
    Int,
    Float,
    Fun(Vec<Self>, Box<Self>),
    Tuple(Vec<Self>),
    Array(Box<Self>, Option<usize>),
}

impl core::hash::Hash for ConcTy {
    fn hash<H: core::hash::Hasher>(&self, ra_expand_state: &mut H) {
        core::mem::discriminant(self).hash(ra_expand_state);
        match self {
            ConcTy::Unit => {}
            ConcTy::Bool => {}
            ConcTy::Int => {}
            ConcTy::Float => {}
            ConcTy::Fun(f0, f1) => {
                f0.hash(ra_expand_state);
                f1.hash(ra_expand_state);
            }
            ConcTy::Tuple(f0) => {
                f0.hash(ra_expand_state);
            }
            ConcTy::Array(f0, _) => {
                f0.hash(ra_expand_state);
            }
        }
    }
}

impl PartialEq for ConcTy {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Fun(l0, l1), Self::Fun(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::Tuple(l0), Self::Tuple(r0)) => l0 == r0,
            (Self::Array(l0, _), Self::Array(r0, _)) => l0 == r0,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl ConcTy {
    /// Returns `true` if the conc ty is [`Unit`].
    ///
    /// [`Unit`]: ConcTy::Unit
    #[must_use]
    pub fn is_unit(&self) -> bool {
        matches!(self, Self::Unit)
    }
    pub fn as_nth(&self, n: usize) -> Option<Self> {
        match self {
            ConcTy::Tuple(ts) => ts.get(n).cloned(),
            ConcTy::Array(e, _) => Some(*e.to_owned()),
            _ => None,
        }
    }

    pub fn as_array(&self) -> Option<&Self> {
        if let Self::Array(t, _) = self {
            Some(t)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    C(CTy),
    V(Rc<RefCell<TypeVar>>),
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::C(c) => write!(f, "{c}"),
            Ty::V(v) => write!(f, "{}", &*v.borrow()),
        }
    }
}

impl Default for Ty {
    fn default() -> Self {
        Self::C(Default::default())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CTy {
    Unit,
    Bool,
    Int,
    Float,
    Fun(Vec<Ty>, Box<Ty>),
    Tuple(Vec<Ty>),
    Array(Box<Ty>, Cell<Option<usize>>),
}

impl Default for CTy {
    fn default() -> Self {
        Self::Unit
    }
}

impl Display for CTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CTy::Unit => write!(f, "()"),
            CTy::Bool => write!(f, "bool"),
            CTy::Int => write!(f, "int"),
            CTy::Float => write!(f, "float"),
            CTy::Fun(ts, r) => {
                write!(
                    f,
                    "(({}) -> {r})",
                    ts.iter()
                        .map(|t| format!("{t}"))
                        .collect::<Vec<String>>()
                        .join(" * ")
                )
            }
            CTy::Tuple(ts) => {
                write!(
                    f,
                    "({})",
                    ts.iter()
                        .map(|t| format!("{t}"))
                        .collect::<Vec<String>>()
                        .join(" * ")
                )
            }
            CTy::Array(t, s) => write!(
                f,
                "[{t}; {}]",
                match s.get() {
                    Some(s) => format!("{s}"),
                    None => "?".to_string(),
                }
            ),
        }
    }
}

impl From<ConcTy> for CTy {
    fn from(value: ConcTy) -> Self {
        match value {
            ConcTy::Unit => Self::Unit,
            ConcTy::Bool => Self::Bool,
            ConcTy::Int => Self::Int,
            ConcTy::Float => Self::Float,
            ConcTy::Fun(ts, t) => Self::Fun(
                ts.into_iter().map(|cc| Ty::C(cc.into())).collect(),
                Box::new(Ty::C((*t).into())),
            ),
            ConcTy::Tuple(ts) => Self::Tuple(ts.into_iter().map(|cc| Ty::C(cc.into())).collect()),
            ConcTy::Array(t, a) => Self::Array(Box::new(Ty::C((*t).into())), Cell::new(a)),
        }
    }
}

impl From<FnTy> for CTy {
    fn from(value: FnTy) -> Self {
        Self::Fun(
            value.arg.into_iter().map(|cc| Ty::C(cc.into())).collect(),
            Box::new(Ty::C(value.ret.into())),
        )
    }
}

impl Display for ConcTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConcTy::Unit => write!(f, "()"),
            ConcTy::Bool => write!(f, "bool"),
            ConcTy::Int => write!(f, "int"),
            ConcTy::Float => write!(f, "float"),
            ConcTy::Fun(ts, r) => {
                write!(
                    f,
                    "(({}) -> {r})",
                    ts.iter()
                        .map(|t| format!("{t}"))
                        .collect::<Vec<String>>()
                        .join(" * ")
                )
            }
            ConcTy::Tuple(ts) => {
                write!(
                    f,
                    "({})",
                    ts.iter()
                        .map(|t| format!("{t}"))
                        .collect::<Vec<String>>()
                        .join(" * ")
                )
            }
            ConcTy::Array(t, s) => write!(
                f,
                "[{t}; {}]",
                match s {
                    Some(s) => format!("{s}"),
                    None => "?".to_string(),
                }
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnTy {
    pub arg: Vec<ConcTy>,
    pub ret: ConcTy,
}

impl Display for FnTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.arg
                .iter()
                .map(|c| format!("{c}"))
                .collect::<Vec<_>>()
                .join(" * ")
        )?;
        write!(f, " -> {}", self.ret)
    }
}

impl Ty {
    pub fn new_typevar() -> Self {
        Ty::V(Rc::new(RefCell::new(TypeVar::new())))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeVar {
    C(CTy),
    V(TypeVarSymbol),
}

impl fmt::Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeVar::C(c) => write!(f, "{c}"),
            TypeVar::V(TypeVarSymbol(id)) => write!(f, "tyvar${id}"),
        }
    }
}

impl TypeVar {
    pub fn new() -> Self {
        Self::V(TypeVarSymbol::new())
    }
    fn resolve(&mut self, concrete: impl Into<CTy>) {
        *self = TypeVar::C(concrete.into());
    }
    fn as_symbol(&self) -> Option<TypeVarSymbol> {
        if let Self::V(s) = self {
            Some(s.clone())
        } else {
            None
        }
    }
    fn as_c(&self) -> Option<CTy> {
        if let Self::C(v) = self {
            Some(v.clone())
        } else {
            None
        }
    }
}

impl Default for TypeVar {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeVarSymbol(usize);

impl TypeVarSymbol {
    pub fn new() -> Self {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        Self(COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

impl Default for TypeVarSymbol {
    fn default() -> Self {
        Self::new()
    }
}

impl Ty {
    pub fn deref_typevar(&mut self, equivs: &mut TypeVarEquivs) {
        use CTy::*;
        match self {
            Ty::C(inner) => match inner {
                Fun(t1s, t2) => {
                    for t1 in t1s {
                        t1.deref_typevar(equivs);
                    }
                    t2.deref_typevar(equivs);
                }
                Tuple(ts) => {
                    for t in ts {
                        t.deref_typevar(equivs);
                    }
                }
                Array(t, ..) => t.deref_typevar(equivs),
                _ => (),
            },
            Ty::V(r) => {
                *self = Self::C('c: {
                    if let TypeVar::C(t) = &mut *r.borrow_mut() {
                        t.deref_typevar(equivs);
                        break 'c t.clone();
                    }
                    log::warn!("uninstantiated type variable found: {r:?}; assuming it `int`.");
                    equivs.resolve_typevar(r.clone(), CTy::Int);
                    CTy::Int
                })
            }
        }
    }
    pub fn as_concty(&self) -> Option<ConcTy> {
        match self {
            Ty::C(c) => c.as_concty(),
            Ty::V(v) => {
                let v: &TypeVar = &v.borrow();
                match v {
                    TypeVar::C(c) => c.as_concty(),
                    _ => None,
                }
            }
        }
    }
}

impl CTy {
    pub fn deref_typevar(&mut self, equivs: &mut TypeVarEquivs) {
        use CTy::*;
        match self {
            Fun(t1s, t2) => {
                for t1 in t1s {
                    t1.deref_typevar(equivs);
                }
                t2.deref_typevar(equivs);
            }
            Tuple(ts) => {
                for t in ts {
                    t.deref_typevar(equivs);
                }
            }
            Array(t, ..) => t.deref_typevar(equivs),
            _ => (),
        }
    }
    pub fn as_concty(&self) -> Option<ConcTy> {
        Some(match self {
            CTy::Unit => ConcTy::Unit,
            CTy::Bool => ConcTy::Bool,
            CTy::Int => ConcTy::Int,
            CTy::Float => ConcTy::Float,
            CTy::Fun(ts, t) => ConcTy::Fun(
                ts.iter().map(|t| t.as_concty()).collect::<Option<_>>()?,
                Box::new(t.as_concty()?),
            ),
            CTy::Tuple(ts) => {
                ConcTy::Tuple(ts.iter().map(|t| t.as_concty()).collect::<Option<_>>()?)
            }
            CTy::Array(t, a) => ConcTy::Array(Box::new(t.as_concty()?), a.get()),
        })
    }

    /// Returns `true` if the conc ty is [`Unit`].
    ///
    /// [`Unit`]: CTy::Unit
    #[must_use]
    pub fn is_unit(&self) -> bool {
        matches!(self, Self::Unit)
    }
}

impl TypeVar {
    /// Checks if type variable r1 occurs in ty.
    pub fn occur(&self, equivs: &TypeVarEquivs, ty: Ty) -> bool {
        match ty {
            Ty::C(inner) => self.occur_c(equivs, inner),
            Ty::V(r2) => {
                if let Some(ty) = r2.borrow().as_c() {
                    return self.occur_c(equivs, ty);
                }
                equivs.is_equiv(self, &r2.borrow())
            }
        }
    }
    /// Checks if type variable r1 occurs in ty.
    pub fn occur_c(&self, equivs: &TypeVarEquivs, ty: CTy) -> bool {
        macro_rules! occur_list {
            ($ls:expr) => {
                $ls.into_iter().any(|ty| self.occur(equivs, ty))
            };
        }
        match ty {
            CTy::Fun(t2s, t2) => occur_list!(t2s) || self.occur(equivs, (*t2).clone()),
            CTy::Tuple(t2s) => occur_list!(t2s),
            CTy::Array(t2, ..) => self.occur(equivs, (*t2).clone()),
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GroupId(usize);

impl GroupId {
    fn new() -> Self {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        Self(COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

impl Default for GroupId {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Default)]
pub struct TypeVarEquivs {
    equiv_map: HashMap<GroupId, Vec<Rc<RefCell<TypeVar>>>>,
    uf: UnionFind<TypeVarSymbol, GroupId>,
}

impl TypeVarEquivs {
    fn is_equiv(&self, v1: &TypeVar, v2: &TypeVar) -> bool {
        self.uf
            .is_equiv(&v1.as_symbol().unwrap(), &v2.as_symbol().unwrap())
            .unwrap_or(false)
    }
    fn insert_equiv(&mut self, v1: Rc<RefCell<TypeVar>>, v2: Rc<RefCell<TypeVar>>) {
        let key1 = v1.borrow().as_symbol().unwrap();
        let key2 = v2.borrow().as_symbol().unwrap();

        if self.uf.get_root_id(&key1).is_none() {
            let gid = GroupId::new();
            self.uf.make_set(key1.clone(), gid);
            self.equiv_map.entry(gid).or_default().push(v1);
        }

        if self.uf.get_root_id(&key2).is_none() {
            let gid = GroupId::new();
            self.uf.make_set(key2.clone(), gid);
            self.equiv_map.entry(gid).or_default().push(v2);
        }

        match self.uf.union(&key1, &key2).unwrap() {
            UnionResult::Merged { new, old } => {
                if let Some(v) = self.equiv_map.remove(&old) {
                    self.equiv_map.entry(new).or_default().extend(v)
                };
            }
            UnionResult::Unchanged { common: _ } => (),
        }
    }
    fn resolve_typevar(&mut self, v: Rc<RefCell<TypeVar>>, concrete: impl Into<CTy>) {
        let concrete = concrete.into();
        let key = v.borrow().as_symbol().unwrap();
        if let Some(gid) = self.uf.get_root_id(&key) {
            if let Some(equivs) = self.equiv_map.get(&gid) {
                for r in equivs {
                    r.borrow_mut().resolve(concrete.clone())
                }
            }
        } else {
            v.borrow_mut().resolve(concrete);
        }
    }
}

#[derive(Debug, Clone)]
pub enum UnifyError {
    Unify(Ty, Ty),
    MismatchArg(usize, usize),
    Occur(TypeVar, Ty),
}

impl fmt::Display for UnifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnifyError::Unify(t1, t2) => write!(f, "cannot satisfy constr `{t1}` == `{t2}`"),
            UnifyError::MismatchArg(a, b) => write!(f, "mismatch length {a} != {b}"),
            UnifyError::Occur(v, t) => write!(f, "`{v}` occurs in `{t}`"),
        }
    }
}

/// "eagerly" deciding type.
pub fn unify(equivs: &mut TypeVarEquivs, t1: &Ty, t2: &Ty) -> Result<(), UnifyError> {
    match t1 {
        Ty::C(t1) => unify_tc(equivs, t2, t1),
        Ty::V(l) => match t2 {
            Ty::V(r) => {
                if let Some(c) = l.borrow().as_c() {
                    return unify_tyvarc(equivs, r.clone(), c);
                }
                if let Some(c) = r.borrow().as_c() {
                    return unify_tyvarc(equivs, l.clone(), c);
                }
                equivs.insert_equiv(l.clone(), r.clone());
                Ok(())
            }
            Ty::C(t2) => unify_tc(equivs, t1, t2),
        },
    }
}

/// "eagerly" deciding type.
pub fn unify_tc(equivs: &mut TypeVarEquivs, t1: &Ty, t2: &CTy) -> Result<(), UnifyError> {
    match t1 {
        Ty::C(t1) => unify_cc(equivs, t1.clone(), t2.clone()),
        Ty::V(r) => unify_tyvarc(equivs, r.clone(), t2.clone()),
    }
}

fn unify_tyvarc(
    equivs: &mut TypeVarEquivs,
    t1: Rc<RefCell<TypeVar>>,
    t2: CTy,
) -> Result<(), UnifyError> {
    if let Some(c1) = t1.borrow().as_c() {
        return unify_cc(equivs, c1, t2);
    }
    if t1.borrow().occur_c(equivs, t2.clone()) {
        return Err(UnifyError::Occur(t1.borrow().clone(), Ty::C(t2)));
    }
    equivs.resolve_typevar(t1, t2);
    Ok(())
}

fn unify_cc(equivs: &mut TypeVarEquivs, t1: CTy, t2: CTy) -> Result<(), UnifyError> {
    macro_rules! unify_seq {
        ($t1s:expr, $t2s: expr) => {
            let n = $t1s.len();
            let m = $t2s.len();
            if n != m {
                return Err(UnifyError::MismatchArg(n, m));
            }
            for (t1, t2) in $t1s.iter().zip($t2s.iter()) {
                unify(equivs, t1, t2)?;
            }
        };
    }
    match (t1, t2) {
        (CTy::Unit, CTy::Unit) => Ok(()),
        (CTy::Bool, CTy::Bool) => Ok(()),
        (CTy::Int, CTy::Int) => Ok(()),
        (CTy::Float, CTy::Float) => Ok(()),
        (CTy::Fun(t1s, t1_), CTy::Fun(t2s, t2_)) => {
            unify_seq!(t1s, t2s);
            unify(equivs, &t1_, &t2_)
        }
        (CTy::Tuple(t1s), CTy::Tuple(t2s)) => {
            unify_seq!(t1s, t2s);
            Ok(())
        }
        (CTy::Array(t1, s1), CTy::Array(t2, s2)) => {
            unify(equivs, &t1, &t2)?;
            match (s1.get(), s2.get()) {
                (None, Some(v)) => s1.set(Some(v)),
                (Some(v), None) => s2.set(Some(v)),
                (Some(v1), Some(v2)) => match v1.cmp(&v2) {
                    std::cmp::Ordering::Less => s1.set(Some(v2)),
                    std::cmp::Ordering::Equal => (),
                    std::cmp::Ordering::Greater => s2.set(Some(v1)),
                },
                _ => (),
            }
            Ok(())
        }
        (t1, t2) => Err(UnifyError::Unify(Ty::C(t1), Ty::C(t2))),
    }
}
