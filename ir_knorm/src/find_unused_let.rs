use std::{cell::RefCell, rc::Rc};
use typedefs::{IfBranch, IfCond, IfExpr, MaybeConst};

use crate::{Continue, IrNode, PathState};

pub fn find_unused_let(node: &IrNode, st: &mut PathState) {
    st.clear_usage();
    enum ModifyEnv<'a, 'b> {
        Root(&'b IrNode<'a>),
        Walk(Rc<RefCell<IrNode<'a>>>),
    }
    let mut stack: Vec<ModifyEnv> = Vec::new();
    use ModifyEnv::*;
    stack.push(Root(node));

    fn mu<'a, 'b>(r: &Rc<RefCell<IrNode<'a>>>) -> ModifyEnv<'a, 'b> {
        Walk(r.clone())
    }

    while let Some(m) = stack.pop() {
        match m {
            Root(node) => visit_node(node, &mut stack, st),
            Walk(node) => visit_node(&node.borrow(), &mut stack, st),
        }
        fn visit_node<'a>(
            node: &IrNode<'a>,
            stack: &mut Vec<ModifyEnv<'a, '_>>,
            st: &mut PathState,
        ) {
            match node {
                IrNode::Const(_) => (),
                IrNode::IUnOp(_, i) | IrNode::FUnOp(_, i) => {
                    st.use_of_var(i);
                }
                IrNode::Var(i) => {
                    st.use_of_var(i);
                }
                IrNode::BBinOp(_, i1, i2) | IrNode::FBinOp(_, i1, i2) => {
                    st.use_of_var(i1);
                    st.use_of_var(i2);
                }
                IrNode::FTerOp(_, i1, i2, i3) => {
                    st.use_of_var(i1);
                    st.use_of_var(i2);
                    st.use_of_var(i3);
                }
                IrNode::IBinOp(_, i1, i2) => {
                    st.use_of_var(i1);
                    if let Some(i2) = i2.as_variable() {
                        st.use_of_var(i2);
                    }
                }
                IrNode::If(IfExpr {
                    cond,
                    clauses: IfBranch::ThenElse { then_, else_ },
                }) => {
                    match cond {
                        IfCond::Bin { lhs, rhs, .. } => {
                            st.use_of_var(lhs);
                            st.use_of_var(rhs);
                        }
                        IfCond::Un { lhs, .. } => {
                            st.use_of_var(lhs);
                        }
                    }
                    stack.push(mu(else_));
                    stack.push(mu(then_));
                }
                IrNode::Let(_, e1, e2) => {
                    stack.push(mu(e2));
                    stack.push(mu(e1));
                }
                IrNode::LetRec(fundef, e) => {
                    stack.push(mu(e));
                    stack.push(mu(&fundef.body));
                }
                IrNode::LetTuple(_, i, e) => {
                    st.use_of_var(i);
                    stack.push(mu(e));
                }
                IrNode::Loop(Continue(_, is), e) => {
                    for (_, i) in is.iter() {
                        st.use_of_var(i);
                    }
                    stack.push(mu(e));
                }
                IrNode::Continue(Continue(_, is)) => {
                    for (_, i) in is.iter() {
                        st.use_of_var(i);
                    }
                }
                IrNode::App(i, is) => {
                    st.use_of_var(i);
                    for i in is.iter() {
                        st.use_of_var(i);
                    }
                }
                IrNode::Tuple(is) => {
                    for i in is.iter() {
                        if let MaybeConst::Variable(i) = i {
                            st.use_of_var(&i.name);
                        }
                    }
                }
                IrNode::Get(i1, i2) => {
                    st.use_of_var(&i1.name);
                    if let Some(i2) = i2.as_variable() {
                        st.use_of_var(i2);
                    }
                }
                IrNode::Set(i1, i2, i3) => {
                    st.use_of_var(&i1.name);
                    if let Some(i2) = i2.as_variable() {
                        st.use_of_var(i2);
                    }
                    st.use_of_var(i3);
                }
                IrNode::ArrayMake(i1, i2) => {
                    if let Some(i1) = i1.as_variable() {
                        st.use_of_var(i1);
                    }
                    if let Some(i2) = i2.as_variable() {
                        st.use_of_var(&i2.name);
                    }
                }
                IrNode::Pervasive(_, is) => {
                    for i in is.iter() {
                        st.use_of_var(&i.var.name);
                    }
                }
                IrNode::PrintInt(i) => {
                    if let Some(i) = i.as_variable() {
                        st.use_of_var(i);
                    }
                }
            }
        }
    }
}
