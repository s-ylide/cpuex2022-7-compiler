use std::{cell::RefCell, collections::HashMap, rc::Rc};

use typedefs::{IdentSymbol, IfBranch, IfExpr, VarDef};

use crate::{FunDef, IrNode, PathState};

use bitvec::prelude::*;

type ArgIndex = BitArr!(for 10);

/// eliminates unused let.
pub fn elim_unused<'a, 'b>(node: &'b mut IrNode<'a>, st: &mut PathState) {
    let mut stack: Vec<&'b mut IrNode<'a>> = Vec::new();
    stack.push(node);
    let mut unused_arg_map: HashMap<IdentSymbol, ArgIndex> = HashMap::new();

    fn mu<T>(r: &mut Rc<RefCell<T>>) -> &mut T {
        Rc::get_mut(r).unwrap().get_mut()
    }

    while let Some(node) = stack.pop() {
        match node {
            IrNode::Let(VarDef { name, .. }, e1, e2)
                if st.is_unused(name) && !e1.borrow().has_effect() =>
            {
                log::debug!("eliminating `let {name} = ..`");
                *node = e2.take();
                st.did_modify();
                stack.push(node);
            }
            IrNode::Let(_, e1, e2)
            | IrNode::If(IfExpr {
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
            IrNode::LetRec(
                FunDef {
                    var: VarDef { name, .. },
                    ..
                },
                e,
            ) if st.is_unused(name) => {
                log::debug!("eliminating `let rec {name} = ..`");
                *node = e.take();
                st.did_modify();
                stack.push(node);
            }
            IrNode::LetRec(def, e) => {
                let mut unused_arg = BitArray::ZERO;
                for (index, a) in def.args.iter().enumerate() {
                    if st.is_unused(a) {
                        unused_arg.set(index, true);
                    }
                }
                let mut iter = unused_arg.iter().by_vals();
                def.args.retain(|_| !iter.next().unwrap());
                unused_arg_map.insert(*def.var.name.id(), unused_arg);
                let body = &mut def.body;
                stack.push(mu(e));
                stack.push(mu(body));
            }
            IrNode::LetTuple(_, _, e) => {
                stack.push(mu(e));
            }
            IrNode::Loop(.., e) => {
                stack.push(mu(e));
            }
            IrNode::App(f, args) => {
                if let Some(arg_map) = unused_arg_map.get(f) {
                    let mut iter = arg_map.iter().by_vals();
                    args.retain(|_| !iter.next().unwrap());
                }
            }
            _ => (),
        }
    }
}
