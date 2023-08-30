use ast::*;

/// recognize some library function as primitive.
pub fn recognize_primitive<'node, 'input>(e: &'node mut Expr<'input>) {
    let mut stack: Vec<&'node mut ExprKind<'input>> = vec![e];
    while let Some(node) = stack.pop() {
        match node {
            ExprKind::App(e1, es) if let Some((&"fless", _)) = e1.as_libfun() => {
                let mut it = std::mem::take(es).into_iter();
                let arg0 = it.next().unwrap();
                let arg1 = it.next().unwrap();
                *node = ExprKind::BinOp(
                    BinOpKind::FBinOp(FBinOpKind::Fless),
                    Box::new(arg0),
                    Box::new(arg1),
                );
                stack.push(node);
            }
            ExprKind::App(e1, es) if let Some((s @ (&"fneg" | &"fiszero" | &"fispos" | &"fisneg"), _)) = e1.as_libfun()  => {
                let mut it = std::mem::take(es).into_iter();
                let arg0 = it.next().unwrap();
                let u = match *s {
                    "fneg" => UnOpKind::FNeg,
                    "fiszero" => UnOpKind::Fiszero,
                    "fispos" => UnOpKind::Fispos,
                    "fisneg" => UnOpKind::Fisneg,
                    _ => unreachable!()
                };
                *node = ExprKind::UnOp(
                    u,
                    Box::new(arg0),
                );
                stack.push(node);
            }
            ExprKind::App(e1, es) => {
                stack.extend(es.iter_mut().map(|e| &mut ***e));
                stack.push(e1);
            }
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
            ExprKind::Set(e1, e2, e3) | ExprKind::If(e1, e2, e3) => {
                stack.push(e3);
                stack.push(e2);
                stack.push(e1);
            }
            ExprKind::Tuple(es) => {
                stack.extend(es.iter_mut().map(|e| &mut ***e));
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
