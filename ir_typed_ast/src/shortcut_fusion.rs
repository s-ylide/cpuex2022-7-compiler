use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
};

use ast::*;
#[cfg(feature = "isa_2nd")]
use ordered_float::NotNan;
use span::Spanned;
use ty::{CTy, Ty};

thread_local! {
    static SHORTCUT_FUSIONS: RefCell<ShortcutFusionMap> = RefCell::new(create_sfmap(available_shortcut_fusions()));
}

enum FusionExpr {
    Raw(&'static str, HashMap<Ident<'static>, Ty>),
    Expr(ast::Expr<'static>),
}

fn available_shortcut_fusions() -> Vec<ShortcutFusion> {
    use CTy::*;
    use FusionExpr::*;
    macro_rules! env {
        ($($i:ident: $ty:expr,)*) => {
            HashMap::from_iter([$((stringify!($i), Ty::C($ty)),)*])
        };
    }
    let it = [
        (
            Raw(
                "if a_ then not b_ else b_",
                env! {
                    a_: Bool,
                    b_: Bool,
                },
            ),
            Expr(typed_expr(
                ExprKind::BinOp(
                    BinOpKind::IBinOp(IBinOpKind::Xor),
                    Box::new(typed_var("a_", CTy::Bool)),
                    Box::new(typed_var("b_", CTy::Bool)),
                ),
                CTy::Bool,
            )),
        ),
        #[cfg(feature = "isa_2nd")]
        (
            Raw(
                "if x_ > 255 then 255 else if x_ < 0 then 0 else x_",
                env! {
                    x_: Int,
                },
            ),
            Expr(typed_expr(
                ExprKind::BinOp(
                    BinOpKind::IBinOp(IBinOpKind::Max),
                    Box::new(typed_expr(ExprKind::Const(ConstKind::Int(0)), CTy::Int)),
                    Box::new(typed_expr(
                        ExprKind::BinOp(
                            BinOpKind::IBinOp(IBinOpKind::Min),
                            Box::new(typed_var("x_", CTy::Int)),
                            Box::new(typed_expr(ExprKind::Const(ConstKind::Int(255)), CTy::Int)),
                        ),
                        CTy::Int,
                    )),
                ),
                CTy::Int,
            )),
        ),
        (
            Raw(
                "if (x_ + 1) < arr.(i) then e else false",
                env! {
                    x_: Int,
                    arr: Array(Box::new(Ty::C(Int)), Cell::new(None)),
                    i: Int,
                    e: Bool,
                },
            ),
            Raw(
                "if x_ < (arr.(i) - 1) then e else false",
                env! {
                    x_: Int,
                    arr: Array(Box::new(Ty::C(Int)), Cell::new(None)),
                    i: Int,
                    e: Bool,
                },
            ),
        ),
        {
            let env = env! {
                x_: Float,
            };
            (
                Raw(
                    "if fiszero x_ then 0.0 else if fispos x_ then 1.0 else -1.0",
                    env.clone(),
                ),
                Raw("if fiszero x_ then 0.0 else fsgnj 1.0 x_", env),
            )
        },
    ]
    .into_iter();
    #[cfg(feature = "isa_2nd")]
    let it = it.chain([
        (
            Raw(
                "c +. a *. b",
                env! {
                    a: Float,
                    b: Float,
                    c: Float,
                },
            ),
            Expr(typed_expr(
                ExprKind::TerOp(
                    TerOpKind::FTerOp(FTerOpKind::Fmadd),
                    Box::new(typed_var("a", Float)),
                    Box::new(typed_var("b", Float)),
                    Box::new(typed_var("c", Float)),
                ),
                Float,
            )),
        ),
        (
            Raw(
                "a *. b +. c",
                env! {
                    a: Float,
                    b: Float,
                    c: Float,
                },
            ),
            Expr(typed_expr(
                ExprKind::TerOp(
                    TerOpKind::FTerOp(FTerOpKind::Fmadd),
                    Box::new(typed_var("a", Float)),
                    Box::new(typed_var("b", Float)),
                    Box::new(typed_var("c", Float)),
                ),
                Float,
            )),
        ),
        (
            Raw(
                "a *. b -. c",
                env! {
                    a: Float,
                    b: Float,
                    c: Float,
                },
            ),
            Expr(typed_expr(
                ExprKind::TerOp(
                    TerOpKind::FTerOp(FTerOpKind::Fmsub),
                    Box::new(typed_var("a", Float)),
                    Box::new(typed_var("b", Float)),
                    Box::new(typed_var("c", Float)),
                ),
                Float,
            )),
        ),
        (
            Raw(
                "c -. a *. b",
                env! {
                    a: Float,
                    b: Float,
                    c: Float,
                },
            ),
            Expr(typed_expr(
                ExprKind::TerOp(
                    TerOpKind::FTerOp(FTerOpKind::Fnmadd),
                    Box::new(typed_var("a", Float)),
                    Box::new(typed_var("b", Float)),
                    Box::new(typed_var("c", Float)),
                ),
                Float,
            )),
        ),
        (
            Raw(
                "c +. fhalf a",
                env! {
                    a: Float,
                    c: Float,
                },
            ),
            Expr(typed_expr(
                ExprKind::TerOp(
                    TerOpKind::FTerOp(FTerOpKind::Fmadd),
                    Box::new(typed_var("a", Float)),
                    Box::new(typed_expr(
                        ExprKind::Const(ConstKind::Float(NotNan::new(0.5).unwrap())),
                        Float,
                    )),
                    Box::new(typed_var("c", Float)),
                ),
                Float,
            )),
        ),
        (
            Raw(
                "c -. fhalf a",
                env! {
                    a: Float,
                    c: Float,
                },
            ),
            Expr(typed_expr(
                ExprKind::TerOp(
                    TerOpKind::FTerOp(FTerOpKind::Fnmadd),
                    Box::new(typed_var("a", Float)),
                    Box::new(typed_expr(
                        ExprKind::Const(ConstKind::Float(NotNan::new(0.5).unwrap())),
                        Float,
                    )),
                    Box::new(typed_var("c", Float)),
                ),
                Float,
            )),
        ),
    ]);

    it.map(|(lhs, rhs)| ShortcutFusion::new(lhs, rhs)).collect()
}

fn parse_and_typeck(e: FusionExpr) -> Expr<'static> {
    use FusionExpr::*;
    match e {
        Raw(r, env) => {
            let mut e = parser::parse(r).unwrap();
            typing::typeck_with_env_toplevel(&mut e, env).unwrap();
            e
        }
        Expr(e) => e,
    }
}

struct ShortcutFusion {
    lhs: Expr<'static>,
    rhs: Expr<'static>,
}

impl ShortcutFusion {
    fn new(lhs: FusionExpr, rhs: FusionExpr) -> Self {
        Self {
            lhs: parse_and_typeck(lhs),
            rhs: parse_and_typeck(rhs),
        }
    }

    fn match_expr<'input, 'node, 'fusion>(
        &'fusion self,
        e: &'node Expr<'input>,
    ) -> Option<MetaVarSubst<'input, 'node, 'fusion>> {
        let mut subst = MetaVarSubst::new(&self.rhs);
        let mut stack: Vec<(&Expr<'static>, &Expr<'input>)> = vec![(&self.lhs, e)];
        while let Some((pat, e)) = stack.pop() {
            let Typed {
                item: Spanned { item: pat, .. },
                ty: pat_ty,
            } = pat;
            let Typed {
                item: Spanned { item: e_expr, .. },
                ty: e_ty,
            } = e;
            if pat_ty.as_ref().unwrap().as_concty() != e_ty.as_ref().unwrap().as_concty() {
                return None;
            }
            match (pat, e_expr) {
                (ExprKind::Const(c1), ExprKind::Const(c2)) => {
                    if c1 != c2 {
                        return None;
                    }
                }
                (ExprKind::Var(v1), _) if !v1.ends_with('_') => {
                    subst.try_assign(v1, e).then_some(())?;
                }
                (ExprKind::Var(v1), ExprKind::Var(_)) => {
                    subst.try_assign(v1, e).then_some(())?;
                }
                (ExprKind::UnOp(k1, p), ExprKind::UnOp(k2, e)) => {
                    if k1 == k2 {
                        stack.push((p, e));
                    } else {
                        return None;
                    }
                }
                (ExprKind::BinOp(k1, p1, p2), ExprKind::BinOp(k2, e1, e2)) => {
                    if k1 == k2 {
                        stack.push((p2, e2));
                        stack.push((p1, e1));
                    } else {
                        return None;
                    }
                }
                (ExprKind::If(p1, p2, p3), ExprKind::If(e1, e2, e3)) => {
                    stack.push((p3, e3));
                    stack.push((p2, e2));
                    stack.push((p1, e1));
                }
                (ExprKind::Then(p1, p2), ExprKind::Then(e1, e2)) => {
                    stack.push((p2, e2));
                    stack.push((p1, e1));
                }
                (ExprKind::App(p, ps), ExprKind::App(e, es)) => {
                    stack.push((p, e));
                    stack.extend(ps.iter().zip(es));
                }
                (ExprKind::LibFun(p, _), ExprKind::LibFun(e, _)) => {
                    if p != e {
                        return None;
                    }
                }
                (ExprKind::Get(p1, p2), ExprKind::Get(e1, e2)) => {
                    stack.push((p2, e2));
                    stack.push((p1, e1));
                }
                _ => return None,
            }
        }
        Some(subst)
    }
}

struct MetaVarSubst<'input, 'node, 'fusion> {
    map: HashMap<Ident<'static>, &'node Expr<'input>>,
    replacer: &'fusion Expr<'static>,
}

impl<'input, 'node, 'fusion> MetaVarSubst<'input, 'node, 'fusion> {
    fn new(replacer: &'fusion Expr<'static>) -> Self {
        Self {
            map: HashMap::new(),
            replacer,
        }
    }
    fn substitute(&'fusion self) -> Expr<'input> {
        fn substitute_impl<'input, 'fusion>(
            ss: &'fusion MetaVarSubst<'input, '_, 'fusion>,
            replacer: &'fusion Expr<'static>,
        ) -> Expr<'input> {
            macro_rules! ss {
                ($n:ident) => {
                    Box::new(substitute_impl(ss, $n))
                };
                (unbox $n:ident) => {
                    substitute_impl(ss, $n)
                };
                (vec $n:ident) => {
                    $n.iter().map(|n| ss!(unbox n)).collect()
                };
            }
            let Typed {
                item: Spanned { item: e, .. },
                ty,
            } = replacer;
            Typed {
                item: Spanned::somewhere(match e {
                    ExprKind::UnOp(arg0, arg1) => ExprKind::UnOp(*arg0, ss!(arg1)),
                    ExprKind::BinOp(arg0, arg1, arg2) => {
                        ExprKind::BinOp(*arg0, ss!(arg1), ss!(arg2))
                    }
                    ExprKind::TerOp(arg0, arg1, arg2, arg3) => {
                        ExprKind::TerOp(*arg0, ss!(arg1), ss!(arg2), ss!(arg3))
                    }
                    ExprKind::If(arg0, arg1, arg2) => ExprKind::If(ss!(arg0), ss!(arg1), ss!(arg2)),
                    ExprKind::Then(arg0, arg1) => ExprKind::Then(ss!(arg0), ss!(arg1)),
                    ExprKind::Var(arg0) => return ss.get(arg0),
                    ExprKind::LibFun(arg0, arg1) => ExprKind::LibFun(arg0, arg1.clone()),
                    ExprKind::App(arg0, arg1) => ExprKind::App(ss!(arg0), ss!(vec arg1)),
                    ExprKind::Tuple(arg0) => ExprKind::Tuple(ss!(vec arg0)),
                    ExprKind::Let(arg0) => ExprKind::Let(match arg0 {
                        LetKind::LetVar(vd, e1, e2) => {
                            LetKind::LetVar(vd.clone(), ss!(e1), ss!(e2))
                        }
                        LetKind::LetRec(
                            FunDef {
                                var,
                                args,
                                body,
                                ret_ty,
                            },
                            e,
                        ) => LetKind::LetRec(
                            FunDef {
                                var: var.clone(),
                                args: args.clone(),
                                body: ss!(body),
                                ret_ty: ret_ty.clone(),
                            },
                            ss!(e),
                        ),
                        LetKind::LetTuple(vds, e1, e2) => {
                            LetKind::LetTuple(vds.clone(), ss!(e1), ss!(e2))
                        }
                    }),
                    ExprKind::ArrayMake(arg0, arg1) => ExprKind::ArrayMake(ss!(arg0), ss!(arg1)),
                    ExprKind::PrintInt(arg0) => ExprKind::PrintInt(ss!(arg0)),
                    ExprKind::Get(arg0, arg1) => ExprKind::Get(ss!(arg0), ss!(arg1)),
                    ExprKind::Set(arg0, arg1, arg2) => {
                        ExprKind::Set(ss!(arg0), ss!(arg1), ss!(arg2))
                    }
                    other => other.clone(),
                }),
                ty: ty.clone(),
            }
        }
        substitute_impl(self, self.replacer)
    }
    fn try_assign(&mut self, k: Ident<'static>, v: &'node Expr<'input>) -> bool {
        if let Some(vv) = self.map.get(k) {
            let Typed {
                item: Spanned { item: pat, .. },
                ..
            } = vv;
            let Typed {
                item: Spanned { item: e_expr, .. },
                ..
            } = v;
            if pat != e_expr {
                return false;
            }
        }
        self.map.insert(k, v);
        true
    }
    fn get(&'fusion self, k: &'fusion Ident<'static>) -> Expr<'input> {
        (*self
            .map
            .get(k)
            .expect("all metavariable should have been captured real variable"))
        .clone()
    }
}

type ShortcutFusionMap = HashMap<ExprDiscriminant, Vec<ShortcutFusion>>;

fn create_sfmap(scfs: Vec<ShortcutFusion>) -> ShortcutFusionMap {
    let mut m = HashMap::new();
    for scf in scfs {
        m.entry(scf.lhs.discriminant())
            .or_insert_with(Vec::new)
            .push(scf);
    }
    m
}

/// do short cut fusion on expression.
/// do not call before `typing::typeck()`.
pub fn shortcut_fusion<'input, 'node>(e: &'node mut Expr<'input>) {
    let mut stack: Vec<&'node mut Expr<'input>> = vec![e];
    while let Some(node) = stack.pop() {
        let d = node.discriminant();
        if let Some(replaced) = SHORTCUT_FUSIONS.with(|r| {
            r.borrow()
                .get(&d)
                .and_then(|v| v.iter().find_map(|scf| scf.match_expr(node)))
                .map(|ss| ss.substitute())
        }) {
            log::debug!("fusion replaced. {:?}", replaced);
            *node = replaced;
        }
        match &mut ***node {
            ExprKind::PrintInt(e1) | ExprKind::UnOp(_, e1) => {
                stack.push(e1);
            }
            ExprKind::ArrayMake(e1, e2)
            | ExprKind::Get(e1, e2)
            | ExprKind::BinOp(_, e1, e2)
            | ExprKind::Then(e1, e2) => {
                stack.push(e2);
                stack.push(e1);
            }
            ExprKind::TerOp(_, e1, e2, e3)
            | ExprKind::Set(e1, e2, e3)
            | ExprKind::If(e1, e2, e3) => {
                stack.push(e3);
                stack.push(e2);
                stack.push(e1);
            }
            ExprKind::App(e1, es) => {
                stack.extend(es.iter_mut());
                stack.push(e1);
            }
            ExprKind::Tuple(es) => {
                stack.extend(es.iter_mut());
            }
            ExprKind::Let(lk) => match lk {
                LetKind::LetTuple(_, e1, e2) | LetKind::LetVar(_, e1, e2) => {
                    stack.push(e2);
                    stack.push(e1);
                }
                LetKind::LetRec(FunDef { body, .. }, e2) => {
                    stack.push(e2);
                    stack.push(body);
                }
            },
            _ => (),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fusion() {
        let src = "let rec xor x y = if x then not y else y in ()";
        let mut parsed = parser::parse(src).unwrap();
        typing::typeck_with_env_toplevel(&mut parsed, HashMap::new()).unwrap();
        shortcut_fusion(&mut parsed);
        match &**parsed {
            ExprKind::Let(LetKind::LetRec(FunDef { body, .. }, ..)) => match &****body {
                ExprKind::BinOp(BinOpKind::IBinOp(IBinOpKind::Xor), x, y) => {
                    match &****x {
                        ExprKind::Var(x) => assert_eq!(x.item, "x"),
                        _ => unreachable!(),
                    };
                    match &****y {
                        ExprKind::Var(y) => assert_eq!(y.item, "y"),
                        _ => unreachable!(),
                    }
                }
                ExprKind::If(_, _, _) => panic!("fusion failed"),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }
}
