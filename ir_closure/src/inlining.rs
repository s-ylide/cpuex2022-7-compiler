use std::{collections::HashMap, mem};

use typedefs::{Ident, IdentSymbol, IfBranch, IfExpr, MaybeConst, VarDef};

use crate::{IrNode, Prog};

/// inlining argument of function.
///
/// this transform is valid since toplevel has global scope.
pub fn inlining_arg<'a>(prog: &mut Prog<'a>) {
    let mut arg_map: HashMap<IdentSymbol, Vec<Option<VarDef>>> = HashMap::new();
    let mut stack: Vec<&IrNode<'a>> = vec![&prog.tail_expr];
    stack.extend(prog.fundefs.iter().map(|f| &*f.body));

    while let Some(node) = stack.pop() {
        match node {
            IrNode::Let(_, e1, e2)
            | IrNode::If(IfExpr {
                clauses:
                    IfBranch::ThenElse {
                        then_: e1,
                        else_: e2,
                    },
                ..
            }) => {
                stack.push(e2);
                stack.push(e1);
            }
            IrNode::Loop(.., e) => {
                stack.push(e);
            }
            IrNode::ApplyDirectly(f, args) => {
                arg_map
                    .entry(*f.id())
                    .and_modify(|arg_inter| {
                        for (arg_inter_op, arg) in arg_inter.iter_mut().zip(args) {
                            if let Some(arg_inter) = arg_inter_op.as_mut() {
                                if arg_inter.id() != arg.id() {
                                    *arg_inter_op = None;
                                }
                            }
                        }
                    })
                    .or_insert_with(|| args.iter().map(|vd| Some(vd.to_owned())).collect());
            }
            _ => (),
        }
    }
    for args in arg_map.values_mut() {
        for arg in args {
            if let Some(arg_inter) = arg.as_mut() {
                if !prog.toplevel_var_types.contains_key(&arg_inter.name) {
                    *arg = None;
                }
            }
        }
    }
    if arg_map.is_empty() {
        return;
    }
    let mut rename_map = HashMap::new();
    for fundef in &mut prog.fundefs {
        let Some(inv_mask) = arg_map.get(&fundef.name) else { continue; };
        let mut it = inv_mask.iter();
        fundef.args.retain(|arg| {
            if let Some(common) = it.next().unwrap() {
                rename_map.insert(*arg.id(), common.to_owned());
                false
            } else {
                true
            }
        });
    }

    fn rename<'a>(rename_map: &HashMap<IdentSymbol, VarDef<'a>>, ident: &mut VarDef<'a>) {
        if let Some(new) = rename_map.get(ident) {
            *ident = new.to_owned();
        };
    }
    fn rename_ident<'a>(rename_map: &HashMap<IdentSymbol, VarDef<'a>>, ident: &mut Ident<'a>) {
        if let Some(new) = rename_map.get(ident) {
            *ident = new.name.to_owned();
        };
    }

    let mut stack: Vec<&mut IrNode<'a>> = vec![&mut prog.tail_expr];
    stack.extend(prog.fundefs.iter_mut().map(|f| &mut *f.body));

    while let Some(node) = stack.pop() {
        match node {
            IrNode::Let(_, e1, e2)
            | IrNode::If(IfExpr {
                clauses:
                    IfBranch::ThenElse {
                        then_: e1,
                        else_: e2,
                    },
                ..
            }) => {
                stack.push(e2);
                stack.push(e1);
            }
            IrNode::Loop(.., e) => {
                stack.push(e);
            }
            IrNode::ApplyDirectly(f, args) => {
                let inv_mask = arg_map.get(f).unwrap();
                let mut it = inv_mask.iter();
                args.retain(|_| it.next().unwrap().is_none());

                for v in args.iter_mut() {
                    rename(&rename_map, v);
                }
            }
            IrNode::IBinOp(_, i1, MaybeConst::Variable(i2)) => {
                rename_ident(&rename_map, i1);
                rename_ident(&rename_map, i2);
            }
            IrNode::IBinOp(_, i1, _) => {
                rename_ident(&rename_map, i1);
            }
            IrNode::Var(i1) => {
                rename_ident(&rename_map, i1);
            }
            IrNode::Tuple(is) => {
                for i in is.iter_mut().filter_map(MaybeConst::as_variable_mut) {
                    rename_ident(&rename_map, i);
                }
            }
            IrNode::Get(v, n) => {
                rename(&rename_map, v);
                if prog.toplevel_var_types.contains_key(&v.name) {
                    *node = IrNode::GetGlobal(mem::take(&mut v.name), mem::take(n))
                }
            }
            IrNode::Set(v, n, i) => {
                rename(&rename_map, v);
                rename_ident(&rename_map, i);
                if prog.toplevel_var_types.contains_key(&v.name) {
                    *node = IrNode::SetGlobal(mem::take(&mut v.name), mem::take(n), mem::take(i))
                }
            }
            IrNode::ArrayMake(_, MaybeConst::Variable(v)) => {
                rename(&rename_map, v);
            }
            IrNode::SetGlobal(_, _, i) => {
                rename_ident(&rename_map, i);
            }
            _ => (),
        }
    }
}
