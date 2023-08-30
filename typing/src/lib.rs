use ast::{
    BinOpKind, ConstKind, Expr, ExprKind, FunDef, LetKind, TerOpKind, Typed, UnOpKind, VarDef,
};
use pervasives::V_ASM_PERVASIVES;
use span::Span;
use std::{cell::Cell, collections::HashMap, fmt};
use ty::{unify, unify_tc, CTy, FnTy, Ty, TypeVarEquivs, UnifyError};

trait DerefTypeVar {
    fn deref_typevar(&mut self, equivs: &mut TypeVarEquivs);
}

impl DerefTypeVar for VarDef<'_> {
    fn deref_typevar(&mut self, equivs: &mut TypeVarEquivs) {
        let VarDef { name: _, ty } = self;
        ty.deref_typevar(equivs);
    }
}

impl<T: DerefTypeVar> DerefTypeVar for Vec<T> {
    fn deref_typevar(&mut self, equivs: &mut TypeVarEquivs) {
        for e in self {
            e.deref_typevar(equivs);
        }
    }
}

impl DerefTypeVar for FunDef<'_> {
    fn deref_typevar(&mut self, equivs: &mut TypeVarEquivs) {
        let FunDef {
            var,
            args,
            body,
            ret_ty,
        } = self;
        var.deref_typevar(equivs);
        args.deref_typevar(equivs);
        body.deref_typevar(equivs);
        ret_ty.deref_typevar(equivs);
    }
}

impl DerefTypeVar for ExprKind<'_> {
    fn deref_typevar(&mut self, equivs: &mut TypeVarEquivs) {
        use ExprKind::*;
        use LetKind::*;
        match self {
            Let(LetVar(var, e1, e2)) => {
                var.deref_typevar(equivs);
                e1.deref_typevar(equivs);
                e2.deref_typevar(equivs);
            }
            Let(LetTuple(vars, e1, e2)) => {
                vars.deref_typevar(equivs);
                e1.deref_typevar(equivs);
                e2.deref_typevar(equivs);
            }
            Let(LetRec(f, e)) => {
                f.deref_typevar(equivs);
                e.deref_typevar(equivs);
            }
            UnOp(_, e) => e.deref_typevar(equivs),
            BinOp(_, e1, e2) | Then(e1, e2) | Get(e1, e2) | ArrayMake(e1, e2) => {
                e1.deref_typevar(equivs);
                e2.deref_typevar(equivs);
            }
            TerOp(_, e1, e2, e3) | If(e1, e2, e3) | Set(e1, e2, e3) => {
                e1.deref_typevar(equivs);
                e2.deref_typevar(equivs);
                e3.deref_typevar(equivs);
            }
            App(e, es) => {
                e.deref_typevar(equivs);
                for e in es {
                    e.deref_typevar(equivs);
                }
            }
            Tuple(es) => {
                for e in es {
                    e.deref_typevar(equivs);
                }
            }
            Const(_) => (),
            Var(_) => (),
            LibFun(_, _) => (),
            PrintInt(e) => {
                e.deref_typevar(equivs);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeckError {
    Assume(UnifyError, Span),
}

impl fmt::Display for TypeckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeckError::Assume(u, s) => write!(f, "at {s}, failed to unify: {u}"),
        }
    }
}

impl TypeckError {
    fn provide_pos_single(u: UnifyError, s: Span) -> Self {
        Self::Assume(u, s)
    }
}

fn typeck_expr<'input>(
    equivs: &mut TypeVarEquivs,
    env: &HashMap<&'input str, Ty>,
    e: &mut Expr<'input>,
    lib: &HashMap<&'input str, FnTy>,
) -> Result<Ty, TypeckError> {
    macro_rules! invoke {
        ($env:expr, $e:expr) => {
            typeck_expr(equivs, $env, $e, lib)
        };
    }
    macro_rules! assume_type {
        ($e:ident : $ty:expr) => {{
            let t = $ty;
            $e.ty = Some(t.clone());
            let t2 = invoke!(env, $e)?;
            unify(equivs, &t.clone(), &t2)
                .map_err(|e| TypeckError::provide_pos_single(e, $e.span.clone()))?
        }};
    }
    macro_rules! assume_concrete_type {
        ($e:ident : $ty:expr) => {{
            let t = Ty::C($ty);
            let t2 = invoke!(env, $e)?;
            let t_ = unify(equivs, &t.clone(), &t2)
                .map_err(|e| TypeckError::provide_pos_single(e, $e.span.clone()))?;
            $e.ty = Some(t);
            t_
        }};
    }
    macro_rules! typeck_list {
        ($es:expr) => {{
            let mut v = Vec::new();
            for e in $es.iter_mut() {
                v.push(typeck_expr(equivs, env, e, lib)?);
            }
            v
        }};
    }
    use CTy::*;
    let ast::Typed {
        item: span::Spanned {
            item: expr,
            span: _,
        },
        ty,
    } = e;
    let expr_ty = match expr {
        ExprKind::Const(ConstKind::Unit) => Ok(Ty::C(Unit)),
        ExprKind::Const(ConstKind::Bool(_)) => Ok(Ty::C(Bool)),
        ExprKind::Const(ConstKind::Int(_)) => Ok(Ty::C(Int)),
        ExprKind::Const(ConstKind::Float(_)) => Ok(Ty::C(Float)),
        ExprKind::UnOp(UnOpKind::Not, e) => {
            assume_concrete_type!(e: Bool);
            Ok(Ty::C(Bool))
        }
        ExprKind::UnOp(UnOpKind::Neg, e1) => {
            // overload
            let t = invoke!(env, e1)?;
            if let Ty::C(CTy::Float) = t {
                *expr = ExprKind::UnOp(UnOpKind::FNeg, std::mem::take(e1));
                Ok(Ty::C(Float))
            } else {
                unify_tc(equivs, &t, &Int)
                    .map_err(|e| TypeckError::provide_pos_single(e, e1.span.clone()))?;
                Ok(Ty::C(Int))
            }
        }
        ExprKind::UnOp(UnOpKind::FNeg, e) => {
            assume_concrete_type!(e: Float);
            Ok(Ty::C(Float))
        }
        ExprKind::UnOp(..) => {
            unreachable!()
        }
        ExprKind::BinOp(BinOpKind::IBinOp(_), e1, e2) => {
            assume_concrete_type!(e1: Int);
            assume_concrete_type!(e2: Int);
            Ok(Ty::C(Int))
        }
        ExprKind::BinOp(BinOpKind::FBinOp(_), e1, e2) => {
            assume_concrete_type!(e1: Float);
            assume_concrete_type!(e2: Float);
            Ok(Ty::C(Float))
        }
        ExprKind::BinOp(BinOpKind::BBinOp(_), e1, e2) => {
            assume_concrete_type!(e1: Int);
            assume_concrete_type!(e2: Int);
            Ok(Ty::C(Bool))
        }
        ExprKind::TerOp(TerOpKind::FTerOp(_), e1, e2, e3) => {
            assume_concrete_type!(e1: Float);
            assume_concrete_type!(e2: Float);
            assume_concrete_type!(e3: Float);
            Ok(Ty::C(Float))
        }
        ExprKind::If(e1, e2, e3) => {
            assume_concrete_type!(e1: Bool);
            let t2 = invoke!(env, e2)?;
            assume_type!(e3: t2.clone());
            Ok(t2)
        }
        ExprKind::Then(e1, e2) => {
            assume_concrete_type!(e1: Unit);
            invoke!(env, e2)
        }
        ExprKind::Let(LetKind::LetVar(VarDef { name, ty }, e1, e2)) => {
            assume_type!(e1: ty.clone());
            let mut cp_env = env.clone();
            cp_env.insert(name, ty.clone());
            invoke!(&cp_env, e2)
        }
        ExprKind::Var(Typed { item: x, ty }) => {
            if let Some(t) = env.get(x).cloned() {
                *ty = Some(t.clone());
                Ok(t)
            } else if let Some(c) = lib.get(x).cloned() {
                log::debug!("resolved `{x}: {c}` as library function.");
                *expr = ExprKind::LibFun(x, c.clone());
                Ok(Ty::C(c.into()))
            } else {
                panic!("unbound variable found: {x}")
            }
        }
        ExprKind::LibFun(_, _) => unreachable!(),
        ExprKind::Let(LetKind::LetRec(fundef, e2)) => {
            let mut cp_env = env.clone();
            typeck_fundef(equivs, &mut cp_env, fundef, lib)?;
            invoke!(&cp_env, e2)
        }
        ExprKind::App(e, es) => {
            let t = Ty::new_typevar();
            let funtype = CTy::Fun(typeck_list!(es), Box::new(t.clone()));
            assume_concrete_type!(e: funtype);
            Ok(t)
        }
        ExprKind::Tuple(es) => Ok(Ty::C(CTy::Tuple(typeck_list!(es)))),
        ExprKind::Let(LetKind::LetTuple(vds, e1, e2)) => {
            assume_concrete_type!(
                e1:
                CTy::Tuple(
                    vds.iter()
                        .map(|xt| xt.ty.clone())
                        .collect::<Vec<_>>()
                )
            );
            let mut cp_env = env.clone();
            for VarDef { name, ty } in vds.iter() {
                cp_env.insert(name, ty.clone());
            }
            invoke!(&cp_env, e2)
        }
        ExprKind::ArrayMake(e1, e2) => {
            assume_concrete_type!(e1: CTy::Int);
            let c1 = e1.as_const().and_then(|c| c.as_int().map(|c| *c as usize));
            let t = invoke!(env, e2)?;
            Ok(Ty::C(CTy::Array(Box::new(t), Cell::new(c1))))
        }
        ExprKind::Get(e1, e2) => {
            let t = Ty::new_typevar();
            assume_concrete_type!(e1: CTy::Array(Box::new(t.clone()), Cell::new(None)));
            assume_concrete_type!(e2: CTy::Int);
            Ok(t)
        }
        ExprKind::Set(e1, e2, e3) => {
            let t = invoke!(env, e3)?;
            assume_concrete_type!(e1: CTy::Array(Box::new(t), Cell::new(None)));
            assume_concrete_type!(e2: CTy::Int);
            Ok(Ty::C(CTy::Unit))
        }
        ExprKind::PrintInt(e) => {
            assume_concrete_type!(e: CTy::Int);
            Ok(Ty::C(CTy::Unit))
        }
    };
    let t = expr_ty?;
    *ty = Some(t.clone());
    Ok(t)
}

fn typeck_fundef<'input>(
    equivs: &mut TypeVarEquivs,
    env: &mut HashMap<&'input str, Ty>,
    fundef: &mut FunDef<'input>,
    lib: &HashMap<&'input str, FnTy>,
) -> Result<(), TypeckError> {
    let FunDef {
        var,
        args,
        body,
        ret_ty,
    } = fundef;
    let VarDef { name, ty } = var;
    env.insert(name, ty.clone());
    let mut cp_env_body = env.clone();
    for VarDef { name, ty } in args.iter() {
        cp_env_body.insert(name, ty.clone());
    }
    let rt = typeck_expr(equivs, &cp_env_body, body, lib)?;
    unify(equivs, ret_ty, &rt).unwrap();
    unify_tc(
        equivs,
        ty,
        &CTy::Fun(args.iter().map(|xt| xt.ty.clone()).collect(), Box::new(rt)),
    )
    .map_err(|e| TypeckError::provide_pos_single(e, Default::default()))
}

thread_local! {
    pub static LIB_CACHE: HashMap<&'static str, FnTy> = V_ASM_PERVASIVES.iter().map(|(name, t)| (*name, t.sig.get_ty())).collect();
}

/// type check and name resolution
pub fn typeck(e: &mut Expr) -> Result<(), TypeckError> {
    let env = HashMap::new();
    let (mut equivs, typed) = typeck_with_env_toplevel(e, env)?;
    unify_tc(&mut equivs, &typed, &CTy::Unit)
        .map_err(|err| TypeckError::Assume(err, e.span.clone()))
}

pub fn typeck_with_env_toplevel<'input>(
    e: &mut Expr<'input>,
    env: HashMap<&'input str, Ty>,
) -> Result<(TypeVarEquivs, Ty), TypeckError> {
    let mut equivs = Default::default();
    let lib: HashMap<_, _> =
        LIB_CACHE.with(|m| m.iter().map(|(name, t)| (*name, t.clone())).collect());
    let typed = typeck_expr(&mut equivs, &env, e, &lib)?;
    e.deref_typevar(&mut equivs);
    Ok((equivs, typed))
}

pub fn typeck_with_env<'input>(
    e: &mut Expr<'input>,
    env: HashMap<&'input str, Ty>,
) -> Result<(), TypeckError> {
    let mut equivs = Default::default();
    typeck_expr(&mut equivs, &env, e, &HashMap::new())?;
    e.deref_typevar(&mut equivs);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify() {
        let t1 = Ty::C(CTy::Float);
        let mut t2 = Ty::new_typevar();
        let t3 = t2.clone();
        let mut equivs = Default::default();
        unify(&mut equivs, &t1, &t2).unwrap();
        t2.deref_typevar(&mut equivs);
        assert_eq!(t1.as_concty().unwrap(), t3.as_concty().unwrap());
    }
}
