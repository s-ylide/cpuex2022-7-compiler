use std::{
    collections::{HashMap, HashSet},
    rc::Rc,
};
use ty::{ConcTy, Ty};
use typedefs::{Ident, IfBranch, IfExpr, Label, VarDef};

use crate::{FunDef, IrNode, Prog};

struct Flag(bool);

impl Flag {
    fn off(&mut self) -> bool {
        let b = self.0;
        self.0 = false;
        b
    }
    fn new(b: bool) -> Self {
        Self(b)
    }
    fn get(&self) -> bool {
        self.0
    }
}

fn closure_transform_expr<'a, 'b>(
    e: ir_knorm::IrNode<'a>,
    fundefs: &'b mut Vec<FunDef<'a>>,
    toplevel_var_types: &'b mut HashMap<Ident<'a>, Ty>,
    is_toplevel: &mut Flag,
) -> IrNode<'a> {
    use IrNode::*;
    macro_rules! invoke {
        ($e:expr, $t:expr) => {
            Box::new(closure_transform_expr(
                Rc::try_unwrap($e).unwrap().into_inner(),
                fundefs,
                toplevel_var_types,
                $t,
            ))
        };
        ($e: expr) => {
            invoke!($e, &mut Flag::new(false))
        };
    }
    match e {
        ir_knorm::IrNode::Const(c) => Const(c),
        ir_knorm::IrNode::IUnOp(k, x) => IUnOp(k, x),
        ir_knorm::IrNode::FUnOp(k, x) => FUnOp(k, x),
        ir_knorm::IrNode::BBinOp(op, x, y) => BBinOp(op, x, y),
        ir_knorm::IrNode::IBinOp(op, x, y) => IBinOp(op, x, y),
        ir_knorm::IrNode::FBinOp(op, x, y) => FBinOp(op, x, y),
        ir_knorm::IrNode::FTerOp(op, x, y, z) => FTerOp(op, x, y, z),
        ir_knorm::IrNode::If(IfExpr {
            cond,
            clauses: IfBranch::ThenElse { then_, else_ },
        }) => If(IfExpr {
            cond,
            clauses: IfBranch::ThenElse {
                then_: invoke!(then_),
                else_: invoke!(else_),
            },
        }),
        ir_knorm::IrNode::Loop(c, body) => Loop(c, invoke!(body)),
        ir_knorm::IrNode::Continue(c) => Continue(c),
        ir_knorm::IrNode::Let(VarDef { name, ty }, e1, e2) => {
            if e1.borrow().has_effect()
                && !matches!(
                    &*e1.borrow(),
                    ir_knorm::IrNode::Set(..) | ir_knorm::IrNode::ArrayMake(..)
                )
            {
                is_toplevel.off();
            }
            if is_toplevel.get() {
                if let ConcTy::Unit | ConcTy::Tuple(..) | ConcTy::Array(..) =
                    ty.as_concty().unwrap()
                {
                    toplevel_var_types.insert(name.clone(), ty.clone());
                }
            }
            let e1 = closure_transform_expr(
                Rc::try_unwrap(e1).unwrap().into_inner(),
                fundefs,
                toplevel_var_types,
                is_toplevel,
            );
            Let(
                VarDef { name, ty },
                Box::new(e1),
                Box::new(closure_transform_expr(
                    Rc::try_unwrap(e2).unwrap().into_inner(),
                    fundefs,
                    toplevel_var_types,
                    is_toplevel,
                )),
            )
        }
        ir_knorm::IrNode::Var(x) => Var(x),
        ir_knorm::IrNode::LetRec(
            ir_knorm::FunDef {
                var: VarDef { name, ty },
                args,
                body: e1,
            },
            e2,
        ) => {
            is_toplevel.off();
            let e1 = Rc::try_unwrap(e1).unwrap().into_inner();
            let e1 = closure_transform_expr(e1, fundefs, toplevel_var_types, &mut Flag::new(false));
            let r: HashSet<Ident> = args
                .iter()
                .map(|VarDef { name, ty: _ }| name.clone())
                .collect();
            let l: HashSet<Ident> = e1.fv().into_iter().cloned().collect();
            let mut zs: HashSet<Ident> = &l - &r;
            for i in toplevel_var_types.keys() {
                zs.remove(i);
            }
            if !zs.is_empty() {
                unimplemented!("closure {name} has free variable `{zs:?}`.");
            }
            fundefs.push(FunDef {
                name: VarDef {
                    name: name.clone(),
                    ty,
                },
                args,
                captured_vars: vec![],
                body: Box::new(e1),
            });
            let e2_ = closure_transform_expr(
                Rc::try_unwrap(e2).unwrap().into_inner(),
                fundefs,
                toplevel_var_types,
                is_toplevel,
            );
            if e2_.fv().contains(&name) {
                unimplemented!("{name}: closure will have eliminated");
            }
            log::info!("eliminated closure {name} as a normal function.");
            e2_
        }
        ir_knorm::IrNode::App(x, ys) => {
            ApplyDirectly(Label::Ident(x), ys.into_iter().map(|v| v.var).collect())
        }
        ir_knorm::IrNode::Tuple(xs) => Tuple(xs),
        ir_knorm::IrNode::LetTuple(..) => unreachable!(),
        ir_knorm::IrNode::Get(x, y) => {
            if toplevel_var_types.contains_key(&x.name) {
                GetGlobal(x.name, y)
            } else {
                Get(x, y)
            }
        }
        ir_knorm::IrNode::Set(x, y, z) => {
            if toplevel_var_types.contains_key(&x.name) {
                SetGlobal(x.name, y, z.name)
            } else {
                Set(x, y, z.name)
            }
        }
        ir_knorm::IrNode::ArrayMake(x, y) => ArrayMake(x, y),
        ir_knorm::IrNode::Pervasive(x, y) => {
            Pervasive(x, y.into_iter().map(|v| v.var.name).collect())
        }
        ir_knorm::IrNode::PrintInt(i) => PrintInt(i),
    }
}

/// verify there is no function need to form closure
pub fn closure_transform(e: ir_knorm::IrNode) -> Prog {
    let mut fundefs = Vec::new();
    let mut toplevel_var_types = HashMap::new();
    let tail_expr = closure_transform_expr(
        e,
        &mut fundefs,
        &mut toplevel_var_types,
        &mut Flag::new(true),
    );
    Prog {
        fundefs,
        toplevel_var_types,
        tail_expr,
    }
}
