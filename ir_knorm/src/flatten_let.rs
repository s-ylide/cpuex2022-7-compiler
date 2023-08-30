use std::{cell::RefCell, rc::Rc};
use typedefs::{IfBranch, IfExpr, VarDef};

use crate::{FunDef, IrNode, PathState};

pub fn flatten_let(node: &mut IrNode, st: &mut PathState) {
    let mut stack: Vec<&mut IrNode> = Vec::new();
    stack.push(node);

    fn mu<T>(r: &mut Rc<RefCell<T>>) -> &mut T {
        Rc::get_mut(r).unwrap().get_mut()
    }

    while let Some(node) = stack.pop() {
        let skip_let = if let IrNode::Let(_, e1, _) = node {
            !matches!(
                &*e1.borrow(),
                IrNode::Let(..) | IrNode::LetRec(..) | IrNode::LetTuple(..)
            )
        } else {
            false
        };
        if skip_let {
            match node {
                IrNode::Let(.., e1, e2) => {
                    stack.push(mu(e2));
                    stack.push(mu(e1));
                }
                _ => unreachable!(),
            }
            continue;
        }
        match node {
            IrNode::If(IfExpr {
                clauses: IfBranch::ThenElse { then_, else_ },
                ..
            }) => {
                stack.push(mu(else_));
                stack.push(mu(then_));
            }
            IrNode::Let(v, e1, e2) => {
                enum Binding<'a> {
                    Let(VarDef<'a>),
                    LetRec(FunDef<'a>),
                    LetTuple(Vec<VarDef<'a>>, VarDef<'a>),
                }
                use Binding::*;
                // drag up bindings
                let mut binders = Vec::new();
                let mut bindees = Vec::new();
                {
                    enum Control<'a> {
                        Walk(IrNode<'a>),
                        Stop(Binding<'a>),
                    }
                    use Control::*;
                    let mut stack = vec![Stop(Let(std::mem::take(v))), Walk(e1.take())];
                    while let Some(ctrl) = stack.pop() {
                        match ctrl {
                            Walk(node) => match node {
                                IrNode::Let(b1, e1, e2) => {
                                    stack.push(Walk(e2.take()));
                                    stack.push(Stop(Let(b1)));
                                    stack.push(Walk(e1.take()));
                                }
                                IrNode::LetRec(b1, e) => {
                                    stack.push(Walk(e.take()));
                                    stack.push(Stop(LetRec(b1)));
                                }
                                IrNode::LetTuple(b1, b2, e) => {
                                    stack.push(Walk(e.take()));
                                    stack.push(Stop(LetTuple(b1, b2)));
                                }
                                tail => {
                                    bindees.push(tail);
                                }
                            },
                            Stop(b) => {
                                binders.push(b);
                            }
                        }
                    }
                }

                *node = {
                    let mut node = e2.take();

                    fn r<T>(value: T) -> Rc<RefCell<T>> {
                        Rc::new(RefCell::new(value))
                    }

                    while let Some(binder) = binders.pop() {
                        match binder {
                            Let(b1) => {
                                let bindee = bindees.pop().unwrap();
                                node = IrNode::Let(b1, r(bindee), r(node));
                            }
                            LetRec(b1) => {
                                node = IrNode::LetRec(b1, r(node));
                            }
                            LetTuple(b1, b2) => {
                                node = IrNode::LetTuple(b1, b2, r(node));
                            }
                        }
                    }
                    node
                };
                st.did_modify();
                log::debug!("flattened a nested let.");
                stack.push(node);
            }
            IrNode::LetRec(fundef, e) => {
                stack.push(mu(e));
                stack.push(mu(&mut fundef.body));
            }
            IrNode::LetTuple(.., e) => {
                stack.push(mu(e));
            }
            IrNode::Loop(.., e) => {
                stack.push(mu(e));
            }
            _ => (),
        }
    }
}
