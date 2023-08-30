use std::{cell::RefCell, collections::HashMap, rc::Rc};

use typedefs::{Ident, IfBranch, IfExpr};

use crate::{alpha_convert::alpha_convert_with_env, IrNode, PathState};

type InliningMap<'a, 'b> = HashMap<&'b Ident<'a>, (Vec<&'b Ident<'a>>, IrNode<'a>)>;

/// inlining function.
pub fn inlining<'a, 'b>(node: &'b mut IrNode<'a>, st: &mut PathState) {
    enum ModifyEnv<'a, 'b> {
        Bind(&'b Ident<'a>, (Vec<&'b Ident<'a>>, IrNode<'a>)),
        UnBind(&'b Ident<'a>),
        Nop,
    }
    let mut stack: Vec<(Option<&'b mut IrNode<'a>>, ModifyEnv<'a, 'b>)> = Vec::new();
    let mut env = InliningMap::new();
    use ModifyEnv::*;
    stack.push((Some(node), Nop));

    fn mu<T>(r: &mut Rc<RefCell<T>>) -> Option<&mut T> {
        Some(Rc::get_mut(r).unwrap().get_mut())
    }

    while let Some((node, m)) = stack.pop() {
        match m {
            Bind(name, (args, body)) => {
                env.insert(name, (args, body));
            }
            UnBind(ident) => {
                env.remove(ident);
            }
            Nop => (),
        }
        if let Some(node) = node {
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
                    stack.push((mu(e2), Nop));
                    stack.push((mu(e1), Nop));
                }
                IrNode::LetRec(def, e) => {
                    let name = &def.var.name;
                    // check if `def` is really recursive definition
                    let refrain_inline = if cfg!(feature = "inline_all") {
                        def.is_recursive()
                    } else if cfg!(feature = "inline_once") {
                        def.is_recursive() || !(st.is_used_once(name) || def.len() < 600)
                    } else {
                        def.is_recursive() || def.contains_loop()
                    };
                    if refrain_inline {
                        stack.push((mu(e), Nop));
                    } else {
                        stack.push((None, UnBind(name)));
                        stack.push((
                            mu(e),
                            Bind(
                                name,
                                (
                                    def.args.iter().map(|d| &d.name).collect(),
                                    def.body.borrow().cloned(),
                                ),
                            ),
                        ));
                    }
                    stack.push((mu(&mut def.body), Nop));
                }
                IrNode::LetTuple(_, _, e) => {
                    stack.push((mu(e), Nop));
                }
                IrNode::Loop(.., e) => {
                    stack.push((mu(e), Nop));
                }
                IrNode::App(f, args) => {
                    if let Some((params, body)) = env.get(f) {
                        let mut body = body.cloned();
                        let env = params
                            .iter()
                            .map(|i| (*i).clone())
                            .zip(args.iter().map(|a| &a.var.name))
                            .collect();
                        alpha_convert_with_env(&mut body, env);
                        log::debug!("inlining `{f}`");
                        *node = body;
                        st.did_modify();
                    }
                }
                _ => (),
            }
        }
    }
}
