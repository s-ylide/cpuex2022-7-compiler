use std::{cell::RefCell, collections::HashMap, rc::Rc};
use typedefs::{IdentSymbol, IfBranch, IfExpr, MaybeConst};

use crate::{IrNode, PathState};

pub fn find_static_alias(node: &IrNode, st: &mut PathState) {
    enum ResourceState {
        /// array is assigned once
        AssignOnce,
        /// array is assigned in some case
        MaybeAssignOnce,
        /// array is updated after the first assignment
        Updated,
        /// array is accessed with init value
        Accessed,
        /// array is accessed possibly before assigned
        MaybeAccessed,
    }
    use ResourceState::*;
    enum ModifyEnv<'a, 'b> {
        ExitIf,
        /// indicate exit of expression evaluated possibly more than once
        ExitLoops,
        Root(&'b IrNode<'a>),
        Node(Rc<RefCell<IrNode<'a>>>),
    }
    use ModifyEnv::*;
    type InitializedArray = HashMap<(IdentSymbol, i32), ResourceState>;
    let mut initialized_array: InitializedArray = HashMap::new();
    let mut stack: Vec<ModifyEnv> = Vec::new();
    let mut called_once = true;
    let mut if_ctxt = false;
    let mut do_trace = true;
    stack.push(Root(node));

    fn mu<'a, 'b>(r: &Rc<RefCell<IrNode<'a>>>) -> ModifyEnv<'a, 'b> {
        Node(r.clone())
    }

    while let Some(m) = stack.pop() {
        use MaybeConst::*;
        match m {
            ExitIf => {
                if_ctxt = false;
            }
            ExitLoops => {
                called_once = true;
            }
            Node(node) => {
                visit_node(
                    &mut called_once,
                    &node.borrow(),
                    &mut stack,
                    &mut if_ctxt,
                    &mut do_trace,
                    &mut initialized_array,
                    st,
                );
            }
            Root(top) => {
                visit_node(
                    &mut called_once,
                    top,
                    &mut stack,
                    &mut if_ctxt,
                    &mut do_trace,
                    &mut initialized_array,
                    st,
                );
            }
        }
        fn visit_node<'a>(
            called_once: &mut bool,
            node: &IrNode<'a>,
            stack: &mut Vec<ModifyEnv<'a, '_>>,
            if_ctxt: &mut bool,
            do_trace: &mut bool,
            initialized_array: &mut InitializedArray,
            st: &PathState,
        ) {
            if *called_once {
                match node {
                    IrNode::If(IfExpr {
                        clauses: IfBranch::ThenElse { then_, else_ },
                        ..
                    }) => {
                        stack.push(ExitIf);
                        stack.push(mu(else_));
                        stack.push(mu(then_));
                        *if_ctxt = true;
                    }
                    IrNode::Let(.., e1, e2) => {
                        stack.push(mu(e2));
                        stack.push(mu(e1));
                    }
                    IrNode::LetRec(fundef, e) => {
                        stack.push(mu(e));
                        stack.push(ExitLoops);
                        stack.push(mu(&fundef.body));
                        *called_once = false;
                    }
                    IrNode::LetTuple(.., e) => {
                        stack.push(mu(e));
                    }
                    IrNode::Loop(.., e) => {
                        stack.push(ExitLoops);
                        stack.push(mu(e));
                        *called_once = false;
                        *do_trace = false;
                    }
                    IrNode::App(..) => {
                        *do_trace = false;
                    }
                    IrNode::Get(arr, Constant(index)) => {
                        if *do_trace {
                            initialized_array
                                .entry((*arr.id(), *index.as_int().unwrap()))
                                .or_insert(Accessed);
                        }
                    }
                    IrNode::Set(arr, Constant(index), _) => {
                        if !st.is_elim_static(*arr.id(), *index.as_int().unwrap()) {
                            initialized_array
                                .entry((*arr.id(), *index.as_int().unwrap()))
                                .and_modify(|r| {
                                    if let AssignOnce | MaybeAssignOnce = r {
                                        *r = Updated;
                                    }
                                })
                                .or_insert(if !*do_trace {
                                    MaybeAccessed
                                } else if *if_ctxt {
                                    MaybeAssignOnce
                                } else {
                                    AssignOnce
                                });
                        }
                    }
                    _ => (),
                }
            } else {
                match node {
                    IrNode::If(IfExpr {
                        clauses: IfBranch::ThenElse { then_, else_ },
                        ..
                    })
                    | IrNode::Let(.., then_, else_) => {
                        stack.push(mu(else_));
                        stack.push(mu(then_));
                    }
                    IrNode::LetRec(fundef, e) => {
                        stack.push(mu(e));
                        stack.push(mu(&fundef.body));
                    }
                    IrNode::LetTuple(.., e) => {
                        stack.push(mu(e));
                    }
                    IrNode::Loop(.., e) => {
                        stack.push(mu(e));
                    }
                    IrNode::Set(arr, Constant(index), _) => {
                        if !st.is_elim_static(*arr.id(), *index.as_int().unwrap()) {
                            initialized_array
                                .entry((*arr.id(), *index.as_int().unwrap()))
                                .and_modify(|r| {
                                    if let AssignOnce | MaybeAssignOnce = r {
                                        *r = Updated;
                                    }
                                })
                                .or_insert(if !*do_trace {
                                    MaybeAccessed
                                } else {
                                    AssignOnce
                                });
                        }
                    }
                    _ => (),
                }
            }
        }
    }
    for ((name, index), s) in initialized_array {
        if let AssignOnce = s {
            st.can_elim_static(name, index);
        }
    }
}
