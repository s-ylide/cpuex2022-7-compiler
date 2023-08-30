use ast::ConstKind;
use std::{cell::RefCell, rc::Rc};
use typedefs::{IfBranch, IfExpr, MaybeConst};

use crate::IrNode;

/// call before flatten let.
pub fn destruct_tuple(node: &mut IrNode) {
    let mut stack: Vec<&mut IrNode> = Vec::new();
    stack.push(node);

    while let Some(node) = stack.pop() {
        fn mu<T>(r: &mut Rc<RefCell<T>>) -> &mut T {
            Rc::get_mut(r).unwrap().get_mut()
        }
        match node {
            IrNode::If(IfExpr {
                clauses: IfBranch::ThenElse { then_, else_ },
                ..
            }) => {
                stack.push(mu(else_));
                stack.push(mu(then_));
            }
            IrNode::Let(.., e1, e2) => {
                stack.push(mu(e2));
                stack.push(mu(e1));
            }
            IrNode::LetRec(fundef, e) => {
                stack.push(mu(e));
                stack.push(mu(&mut fundef.body));
            }
            IrNode::LetTuple(is, t, e) => {
                *node = {
                    let mut node = e.take();

                    fn r<T>(value: T) -> Rc<RefCell<T>> {
                        Rc::new(RefCell::new(value))
                    }

                    for (i, var) in std::mem::take(is).into_iter().enumerate() {
                        let bindee = IrNode::Get(
                            t.to_owned(),
                            MaybeConst::Constant(ConstKind::Int(i as i32)),
                        );
                        node = IrNode::Let(var, r(bindee), r(node));
                    }
                    node
                };
                stack.push(node);
            }
            IrNode::Loop(.., e) => {
                stack.push(mu(e));
            }
            _ => (),
        }
    }
}
