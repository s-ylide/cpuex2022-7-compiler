use std::{cell::RefCell, rc::Rc};

use typedefs::{Ident, IfBranch, IfExpr, VarDef};

use crate::{alpha_convert::alpha_convert_with_env, Continue, FunDef, IrNode, PathState};

use bitvec::prelude::*;

type ArgIndex = BitArr!(for 10);

/// create loop from tail recursion.
pub fn create_loop<'a, 'b>(node: &'b mut IrNode<'a>, st: &mut PathState) {
    let mut stack: Vec<&'b mut IrNode<'a>> = Vec::new();
    stack.push(node);

    fn mu<T>(r: &mut Rc<RefCell<T>>) -> &mut T {
        Rc::get_mut(r).unwrap().get_mut()
    }

    while let Some(node) = stack.pop() {
        match node {
            IrNode::LetRec(def, e) => {
                let name = &def.var.name;
                let body = &mut def.body;
                if body.borrow().contains(name) {
                    if let Some(tails) = collect_tails(def) {
                        let mut loop_arg_index: ArgIndex = BitArray::ZERO;
                        for tail in tails {
                            loop_arg_index |= tail;
                        }
                        let label = name.updated();
                        let loop_param_old: Vec<_> = def
                            .args
                            .iter()
                            .enumerate()
                            .filter_map(|(i, arg)| {
                                if loop_arg_index[i] {
                                    Some(arg.clone())
                                } else {
                                    None
                                }
                            })
                            .collect();
                        let loop_param: Vec<_> = loop_param_old
                            .iter()
                            .cloned()
                            .map(|mut i| {
                                i.update();
                                i
                            })
                            .collect();
                        replace_tails(def, loop_arg_index, &loop_param, &label);
                        let env = loop_param_old
                            .iter()
                            .map(|vd| vd.name.clone())
                            .zip(loop_param.iter().map(|vd| vd.name.clone()))
                            .collect();

                        alpha_convert_with_env(&mut def.body.borrow_mut(), env);
                        let loop_body = std::mem::take(&mut def.body);

                        fn rr<T>(v: T) -> Rc<RefCell<T>> {
                            Rc::new(RefCell::new(v))
                        }

                        log::debug!("loop created: '{label}");
                        def.body = rr(IrNode::Loop(
                            Continue(label, loop_param.into_iter().zip(loop_param_old).collect()),
                            loop_body,
                        ));
                        st.did_modify();
                    }
                }
                stack.push(mu(e));
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
            IrNode::LetTuple(.., e) | IrNode::Loop(.., e) => {
                stack.push(mu(e));
            }
            _ => (),
        }
    }
}

/// tests if fundef has only tail rec, collecting tail call arguments
fn collect_tails(f: &FunDef) -> Option<Vec<ArgIndex>> {
    enum ModifyEnv<'a, 'b> {
        UnBindLet,
        Root(&'b IrNode<'a>),
        Walk(Rc<RefCell<IrNode<'a>>>),
    }
    let mut stack: Vec<ModifyEnv> = Vec::new();
    use ModifyEnv::*;
    let binding = f.body.borrow();
    stack.push(Root(&binding));

    fn mu<'a, 'b>(r: &Rc<RefCell<IrNode<'a>>>) -> ModifyEnv<'a, 'b> {
        Walk(r.clone())
    }

    let mut tail_args: Vec<ArgIndex> = Vec::new();
    let mut let_depth = 0;

    while let Some(m) = stack.pop() {
        match m {
            Root(node) => visit_node(node, &mut stack, f, &mut tail_args, &mut let_depth)?,
            Walk(node) => visit_node(
                &node.borrow(),
                &mut stack,
                f,
                &mut tail_args,
                &mut let_depth,
            )?,
            UnBindLet => let_depth -= 1,
        }
        fn visit_node<'a, 'b>(
            node: &IrNode<'a>,
            stack: &mut Vec<ModifyEnv<'a, 'b>>,
            f: &'b FunDef<'a>,
            tail_args: &mut Vec<ArgIndex>,
            let_depth: &mut usize,
        ) -> Option<()> {
            match node {
                IrNode::Let(_, e1, e2) => {
                    stack.push(mu(e2));
                    stack.push(UnBindLet);
                    stack.push(mu(e1));
                    *let_depth += 1;
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
                IrNode::App(ff, args) => {
                    if ff == &f.var.name {
                        // found non tail recursion
                        if *let_depth != 0 {
                            return None;
                        }
                        let mut ba = BitArray::ZERO;
                        for (index, (a1, a2)) in f.args.iter().zip(args.iter()).enumerate() {
                            if a1.name != a2.name {
                                ba.set(index, true);
                            }
                        }
                        tail_args.push(ba);
                    }
                }
                _ => (),
            }
            Some(())
        }
    }
    Some(tail_args)
}

/// replaces tail rec into continue
fn replace_tails<'a, 'b>(
    f: &'b mut FunDef<'a>,
    loop_arg_index: ArgIndex,
    loop_param: &[VarDef<'a>],
    label: &Ident<'a>,
) {
    let mut stack: Vec<&'b mut IrNode<'a>> = Vec::new();
    stack.push(mu(&mut f.body));

    fn mu<'a, 'b>(r: &'b mut Rc<RefCell<IrNode<'a>>>) -> &'b mut IrNode<'a> {
        Rc::get_mut(r).unwrap().get_mut()
    }

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
                stack.push(mu(e2));
                stack.push(mu(e1));
            }
            IrNode::LetRec(_, e) | IrNode::LetTuple(.., e) | IrNode::Loop(.., e) => {
                stack.push(mu(e));
            }
            IrNode::App(ff, args) => {
                // `collect_tails()` asserts that this is tail rec
                if ff == &f.var.name {
                    let assign =
                        std::mem::take(args)
                            .into_iter()
                            .enumerate()
                            .filter_map(|(i, arg)| {
                                if loop_arg_index[i] {
                                    Some(arg.var)
                                } else {
                                    None
                                }
                            });
                    *node = IrNode::Continue(Continue(
                        label.to_owned(),
                        loop_param.iter().cloned().zip(assign).collect(),
                    ));
                }
            }
            _ => (),
        }
    }
}
