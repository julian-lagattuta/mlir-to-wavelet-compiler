use std::collections::HashMap;

use wavelet_elab::{
    Expr, FnDef, FnName, Op, Program, Stmt, Tail, Ty, TypeError, TypedVar, UntypedVar, Val,
    ir::Signedness,
};

type TypeEnv = HashMap<String, Ty>;
type Registry<'a> = HashMap<String, &'a FnDef<UntypedVar>>;

pub(crate) fn type_program(program: &Program<UntypedVar>) -> Result<Program<TypedVar>, TypeError> {
    let registry: Registry<'_> = program
        .defs
        .iter()
        .map(|definition| (definition.name.0.clone(), definition))
        .collect();

    let defs = program
        .defs
        .iter()
        .map(|definition| type_function(definition, &registry))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Program { defs })
}

fn type_function(
    definition: &FnDef<UntypedVar>,
    registry: &Registry<'_>,
) -> Result<FnDef<TypedVar>, TypeError> {
    let mut types = definition
        .params
        .iter()
        .map(|parameter| (parameter.name.clone(), parameter.ty.clone()))
        .collect();
    let (body_ty, body) = type_expr(&definition.body, &mut types, registry)?;
    require_same_type(&definition.returns, &body_ty)?;

    Ok(FnDef {
        name: definition.name.clone(),
        params: definition.params.clone(),
        alloc_arrays: definition.alloc_arrays.clone(),
        caps: definition.caps.clone(),
        returns: definition.returns.clone(),
        body,
    })
}

fn type_expr(
    expression: &Expr<UntypedVar>,
    types: &mut TypeEnv,
    registry: &Registry<'_>,
) -> Result<(Ty, Expr<TypedVar>), TypeError> {
    let stmts = expression
        .stmts
        .iter()
        .map(|statement| type_stmt(statement, types, registry))
        .collect::<Result<Vec<_>, _>>()?;
    let (ty, tail) = type_tail(&expression.tail, types, registry)?;
    Ok((ty, Expr { stmts, tail }))
}

fn type_stmt(
    statement: &Stmt<UntypedVar>,
    types: &mut TypeEnv,
    registry: &Registry<'_>,
) -> Result<Stmt<TypedVar>, TypeError> {
    match statement {
        Stmt::LetVal { var, val, fence } => {
            let ty = match val {
                Val::Int(value) if *value < 0 => Ty::Int(Signedness::Signed),
                Val::Int(_) => Ty::Int(Signedness::Unsigned),
                Val::Bool(_) => Ty::Bool,
                Val::Unit => Ty::Unit,
            };
            bind(types, var, ty.clone());
            Ok(Stmt::LetVal {
                var: var.add_type(ty),
                val: val.clone(),
                fence: *fence,
            })
        }
        Stmt::LetOp { vars, op, fence } => type_op(vars, op, *fence, types),
        Stmt::LetCall {
            vars,
            func,
            args,
            fence,
        } => {
            let definition = lookup_function(registry, func)?;
            let typed_args = type_call_args(definition, args, types, "function call")?;
            if vars.len() != 1 {
                return invalid(format!(
                    "function call to {} has wrong number of return bindings",
                    func.0
                ));
            }
            bind(types, &vars[0], definition.returns.clone());
            Ok(Stmt::LetCall {
                vars: vec![vars[0].add_type(definition.returns.clone())],
                func: func.clone(),
                args: typed_args,
                fence: *fence,
            })
        }
    }
}

fn type_op(
    vars: &[UntypedVar],
    op: &Op<UntypedVar>,
    fence: bool,
    types: &mut TypeEnv,
) -> Result<Stmt<TypedVar>, TypeError> {
    match op {
        Op::Add | Op::Sub | Op::Mul | Op::Sdiv | Op::Udiv => {
            require_arity(vars, 3, op)?;
            let lhs = require_int(type_of(types, &vars[0])?, op)?;
            let rhs = require_int(type_of(types, &vars[1])?, op)?;
            let result = Ty::Int(combine_signedness(&lhs, &rhs));
            bind(types, &vars[2], result.clone());
            let typed_op = match op {
                Op::Add => Op::Add,
                Op::Sub => Op::Sub,
                Op::Mul => Op::Mul,
                Op::Sdiv if matches!(result, Ty::Int(Signedness::Unsigned)) => Op::Udiv,
                Op::Sdiv => Op::Sdiv,
                Op::Udiv => Op::Udiv,
                _ => unreachable!(),
            };
            typed_let_op(vars, vec![lhs, rhs, result], typed_op, fence)
        }
        Op::And | Op::Or => {
            require_arity(vars, 3, op)?;
            require_type(type_of(types, &vars[0])?, &Ty::Bool, op)?;
            require_type(type_of(types, &vars[1])?, &Ty::Bool, op)?;
            bind(types, &vars[2], Ty::Bool);
            let typed_op = if matches!(op, Op::And) {
                Op::And
            } else {
                Op::Or
            };
            typed_let_op(vars, vec![Ty::Bool, Ty::Bool, Ty::Bool], typed_op, fence)
        }
        Op::Not => {
            require_arity(vars, 2, op)?;
            require_type(type_of(types, &vars[0])?, &Ty::Bool, op)?;
            bind(types, &vars[1], Ty::Bool);
            typed_let_op(vars, vec![Ty::Bool, Ty::Bool], Op::Not, fence)
        }
        Op::BitAnd | Op::BitOr | Op::BitXor => {
            require_arity(vars, 3, op)?;
            let lhs = require_int(type_of(types, &vars[0])?, op)?;
            let rhs = require_int(type_of(types, &vars[1])?, op)?;
            let result = Ty::Int(combine_signedness(&lhs, &rhs));
            bind(types, &vars[2], result.clone());
            let typed_op = match op {
                Op::BitAnd => Op::BitAnd,
                Op::BitOr => Op::BitOr,
                Op::BitXor => Op::BitXor,
                _ => unreachable!(),
            };
            typed_let_op(vars, vec![lhs, rhs, result], typed_op, fence)
        }
        Op::Shl | Op::Ashr | Op::Lshr => {
            require_arity(vars, 3, op)?;
            let lhs = require_int(type_of(types, &vars[0])?, op)?;
            let rhs = require_int(type_of(types, &vars[1])?, op)?;
            let result = lhs.clone();
            bind(types, &vars[2], result.clone());
            let typed_op = match op {
                Op::Shl => Op::Shl,
                Op::Ashr if matches!(result, Ty::Int(Signedness::Unsigned)) => Op::Lshr,
                Op::Ashr => Op::Ashr,
                Op::Lshr => Op::Lshr,
                _ => unreachable!(),
            };
            typed_let_op(vars, vec![lhs, rhs, result], typed_op, fence)
        }
        Op::SignedLessThan | Op::SignedLessEqual | Op::UnsignedLessThan | Op::UnsignedLessEqual => {
            require_arity(vars, 3, op)?;
            let lhs = require_int(type_of(types, &vars[0])?, op)?;
            let rhs = require_int(type_of(types, &vars[1])?, op)?;
            let unsigned = matches!(combine_signedness(&lhs, &rhs), Signedness::Unsigned);
            bind(types, &vars[2], Ty::Bool);
            let typed_op = match op {
                Op::SignedLessThan if unsigned => Op::UnsignedLessThan,
                Op::SignedLessThan => Op::SignedLessThan,
                Op::SignedLessEqual if unsigned => Op::UnsignedLessEqual,
                Op::SignedLessEqual => Op::SignedLessEqual,
                Op::UnsignedLessThan => Op::UnsignedLessThan,
                Op::UnsignedLessEqual => Op::UnsignedLessEqual,
                _ => unreachable!(),
            };
            typed_let_op(vars, vec![lhs, rhs, Ty::Bool], typed_op, fence)
        }
        Op::Equal | Op::NotEqual => {
            require_arity(vars, 3, op)?;
            let lhs = type_of(types, &vars[0])?;
            let rhs = type_of(types, &vars[1])?;
            if lhs != rhs && !(lhs.is_int() && rhs.is_int()) {
                return invalid(format!("{op:?}"));
            }
            bind(types, &vars[2], Ty::Bool);
            let typed_op = if matches!(op, Op::Equal) {
                Op::Equal
            } else {
                Op::NotEqual
            };
            typed_let_op(vars, vec![lhs, rhs, Ty::Bool], typed_op, fence)
        }
        Op::Load { array, index, len } => {
            require_arity(vars, 1, op)?;
            let index_ty = require_int(type_of(types, index)?, op)?;
            let array_ty = type_of(types, array)?;
            let (array_len, element_ty) = array_parts(&array_ty, "load non array")?;
            if array_len != len {
                return invalid(format!(
                    "load length mismatch (have {}, need {})",
                    array_len.display(),
                    len.display()
                ));
            }
            bind(types, &vars[0], element_ty.clone());
            Ok(Stmt::LetOp {
                vars: vec![vars[0].add_type(element_ty)],
                op: Op::Load {
                    array: array.add_type(array_ty),
                    index: index.add_type(index_ty),
                    len: len.clone(),
                },
                fence,
            })
        }
        Op::Store {
            array,
            index,
            value,
            len,
        } => {
            require_arity(vars, 0, op)?;
            let index_ty = require_int(type_of(types, index)?, op)?;
            let array_ty = type_of(types, array)?;
            let (array_len, element_ty) = array_parts(&array_ty, "store non array")?;
            let value_ty = type_of(types, value)?;
            if value_ty != element_ty
                && !(value_ty.is_int()
                    && element_ty.is_int()
                    && combine_signedness(&value_ty, &element_ty)
                        == element_ty.signedness().unwrap())
            {
                return invalid("store value type");
            }
            if array_len != len {
                return invalid(format!(
                    "store length mismatch (have {}, need {})",
                    array_len.display(),
                    len.display()
                ));
            }
            Ok(Stmt::LetOp {
                vars: vec![],
                op: Op::Store {
                    array: array.add_type(array_ty),
                    index: index.add_type(index_ty),
                    value: value.add_type(value_ty),
                    len: len.clone(),
                },
                fence,
            })
        }
    }
}

fn type_tail(
    tail: &Tail<UntypedVar>,
    types: &TypeEnv,
    registry: &Registry<'_>,
) -> Result<(Ty, Tail<TypedVar>), TypeError> {
    match tail {
        Tail::RetVar(var) => {
            let ty = type_of(types, var)?;
            Ok((ty.clone(), Tail::RetVar(var.add_type(ty))))
        }
        Tail::IfElse {
            cond,
            then_e,
            else_e,
        } => {
            if !matches!(type_of(types, cond)?, Ty::Bool) {
                return invalid("if condition type");
            }
            let (then_ty, then_e) = type_expr(then_e, &mut types.clone(), registry)?;
            let (else_ty, else_e) = type_expr(else_e, &mut types.clone(), registry)?;
            let result_ty = compatible_result_type(&then_ty, &else_ty)?;
            Ok((
                result_ty,
                Tail::IfElse {
                    cond: cond.add_type(Ty::Bool),
                    then_e: Box::new(then_e),
                    else_e: Box::new(else_e),
                },
            ))
        }
        Tail::TailCall { func, args } => {
            let definition = lookup_function(registry, func)?;
            let typed_args = type_call_args(definition, args, &mut types.clone(), "tail call")?;
            Ok((
                definition.returns.clone(),
                Tail::TailCall {
                    func: func.clone(),
                    args: typed_args,
                },
            ))
        }
    }
}

fn type_call_args(
    definition: &FnDef<UntypedVar>,
    args: &[UntypedVar],
    types: &mut TypeEnv,
    call_kind: &str,
) -> Result<Vec<TypedVar>, TypeError> {
    let value_params: Vec<_> = definition
        .params
        .iter()
        .filter(|parameter| !parameter.ty.is_array_ref())
        .collect();
    let array_params: Vec<_> = definition
        .params
        .iter()
        .filter(|parameter| parameter.ty.is_array_ref())
        .collect();
    if args.len() < value_params.len() {
        return invalid(format!(
            "{call_kind} to {} has too few arguments",
            definition.name.0
        ));
    }

    let mut typed_args = Vec::with_capacity(args.len());
    for (parameter, argument) in value_params.iter().zip(args) {
        let actual = type_of(types, argument)?;
        let annotated = if actual.is_int() && parameter.ty.is_int() {
            if argument.0.starts_with("_lit_") {
                bind(types, argument, parameter.ty.clone());
            }
            parameter.ty.clone()
        } else {
            require_same_type(&parameter.ty, &actual)?;
            actual
        };
        typed_args.push(argument.add_type(annotated));
    }

    let array_args = &args[value_params.len()..];
    if array_args.len() != array_params.len() {
        return invalid(format!(
            "{call_kind} to {} has wrong number of array arguments",
            definition.name.0
        ));
    }
    for argument in array_args {
        typed_args.push(argument.add_type(type_of(types, argument)?));
    }
    Ok(typed_args)
}

fn type_of(types: &TypeEnv, var: &UntypedVar) -> Result<Ty, TypeError> {
    types
        .get(&var.0)
        .cloned()
        .or_else(|| matches!(var.0.as_str(), "_unit_literal" | "_unit_ret").then_some(Ty::Unit))
        .ok_or_else(|| TypeError::UndeclaredVar(var.0.clone()))
}

fn bind(types: &mut TypeEnv, var: &UntypedVar, ty: Ty) {
    types.insert(var.0.clone(), ty);
}

fn lookup_function<'a>(
    registry: &'a Registry<'_>,
    name: &FnName,
) -> Result<&'a FnDef<UntypedVar>, TypeError> {
    registry
        .get(&name.0)
        .copied()
        .ok_or_else(|| TypeError::UndefinedFunction(name.0.clone()))
}

fn require_arity(
    vars: &[UntypedVar],
    expected: usize,
    op: &Op<UntypedVar>,
) -> Result<(), TypeError> {
    if vars.len() == expected {
        Ok(())
    } else {
        invalid(format!("{op:?}"))
    }
}

fn require_int(ty: Ty, op: &Op<UntypedVar>) -> Result<Ty, TypeError> {
    if ty.is_int() {
        Ok(ty)
    } else {
        invalid(format!("{op:?}"))
    }
}

fn require_type(ty: Ty, expected: &Ty, op: &Op<UntypedVar>) -> Result<(), TypeError> {
    if &ty == expected {
        Ok(())
    } else {
        invalid(format!("{op:?}"))
    }
}

fn require_same_type(expected: &Ty, found: &Ty) -> Result<(), TypeError> {
    if expected == found {
        Ok(())
    } else {
        Err(TypeError::TypeMismatch {
            expected: TypeError::type_name(expected),
            found: TypeError::type_name(found),
        })
    }
}

fn compatible_result_type(lhs: &Ty, rhs: &Ty) -> Result<Ty, TypeError> {
    if lhs == rhs {
        Ok(lhs.clone())
    } else if lhs.is_int() && rhs.is_int() {
        Ok(Ty::Int(combine_signedness(lhs, rhs)))
    } else {
        require_same_type(lhs, rhs)?;
        unreachable!()
    }
}

fn combine_signedness(lhs: &Ty, rhs: &Ty) -> Signedness {
    match (lhs.signedness(), rhs.signedness()) {
        (Some(Signedness::Unsigned), Some(Signedness::Unsigned)) => Signedness::Unsigned,
        _ => Signedness::Signed,
    }
}

fn array_parts<'a>(
    ty: &'a Ty,
    error: &str,
) -> Result<(&'a wavelet_elab::ir::ArrayLen, Ty), TypeError> {
    match ty {
        Ty::RefShrd { elem, len } | Ty::RefUniq { elem, len } => Ok((len, elem.as_ref().clone())),
        _ => invalid(error),
    }
}

fn typed_let_op(
    vars: &[UntypedVar],
    types: Vec<Ty>,
    op: Op<TypedVar>,
    fence: bool,
) -> Result<Stmt<TypedVar>, TypeError> {
    Ok(Stmt::LetOp {
        vars: vars
            .iter()
            .zip(types)
            .map(|(var, ty)| var.add_type(ty))
            .collect(),
        op,
        fence,
    })
}

fn invalid<T>(op: impl Into<String>) -> Result<T, TypeError> {
    Err(TypeError::InvalidOp { op: op.into() })
}


#[cfg(test)]
mod tests {
    use super::type_program;
    use wavelet_elab::{
        Expr, FnDef, FnName, Op, Program, Stmt, Tail, Ty, TypedVar, UntypedVar, Val,
        ir::{ArrayLen, Signedness},
    };

    fn var(name: &str) -> UntypedVar {
        UntypedVar(name.to_owned())
    }

    #[test]
    fn annotates_statements_calls_and_nested_tails_without_capabilities() {
        let callee = FnDef {
            name: FnName("callee".to_owned()),
            params: vec![TypedVar::new("x", Ty::Int(Signedness::Signed))],
            alloc_arrays: vec![],
            caps: vec![],
            returns: Ty::Int(Signedness::Signed),
            body: Expr::ret(var("x")),
        };
        let caller = FnDef {
            name: FnName("caller".to_owned()),
            params: vec![TypedVar::new("condition", Ty::Bool)],
            alloc_arrays: vec![],
            caps: vec![],
            returns: Ty::Int(Signedness::Signed),
            body: Expr {
                stmts: vec![
                    Stmt::LetVal {
                        var: var("one"),
                        val: Val::Int(1),
                        fence: false,
                    },
                    Stmt::LetCall {
                        vars: vec![var("result")],
                        func: FnName("callee".to_owned()),
                        args: vec![var("one")],
                        fence: false,
                    },
                ],
                tail: Tail::IfElse {
                    cond: var("condition"),
                    then_e: Box::new(Expr::ret(var("result"))),
                    else_e: Box::new(Expr::ret(var("result"))),
                },
            },
        };

        let typed = type_program(&Program {
            defs: vec![callee, caller],
        })
        .unwrap();
        let caller = &typed.defs[1];
        let Stmt::LetCall { vars, args, .. } = &caller.body.stmts[1] else {
            panic!("expected typed call")
        };
        assert_eq!(vars[0].ty, Ty::Int(Signedness::Signed));
        assert_eq!(args[0].ty, Ty::Int(Signedness::Signed));
        let Tail::IfElse { cond, .. } = &caller.body.tail else {
            panic!("expected typed conditional")
        };
        assert_eq!(cond.ty, Ty::Bool);
    }

    #[test]
    fn reports_undeclared_variables() {
        let definition = FnDef {
            name: FnName("bad".to_owned()),
            params: vec![],
            alloc_arrays: vec![],
            caps: vec![],
            returns: Ty::Bool,
            body: Expr::ret(var("missing")),
        };

        let error = type_program(&Program {
            defs: vec![definition],
        })
        .unwrap_err();
        assert!(matches!(error, wavelet_elab::TypeError::UndeclaredVar(name) if name == "missing"));
    }

    #[test]
    fn preserves_operation_signedness_rules() {
        let definition = FnDef {
            name: FnName("add".to_owned()),
            params: vec![],
            alloc_arrays: vec![],
            caps: vec![],
            returns: Ty::Int(Signedness::Unsigned),
            body: Expr {
                stmts: vec![
                    Stmt::LetVal {
                        var: var("one"),
                        val: Val::Int(1),
                        fence: false,
                    },
                    Stmt::LetVal {
                        var: var("two"),
                        val: Val::Int(2),
                        fence: false,
                    },
                    Stmt::LetOp {
                        vars: vec![var("one"), var("two"), var("sum")],
                        op: Op::Add,
                        fence: false,
                    },
                ],
                tail: Tail::RetVar(var("sum")),
            },
        };

        let typed = type_program(&Program {
            defs: vec![definition],
        })
        .unwrap();
        let Stmt::LetOp { vars, .. } = &typed.defs[0].body.stmts[2] else {
            panic!("expected typed operation")
        };
        assert_eq!(vars[2].ty, Ty::Int(Signedness::Unsigned));
    }

    #[test]
    fn types_loads_without_checking_capabilities() {
        let len = ArrayLen::Const(4);
        let array_ty = Ty::RefUniq {
            elem: Box::new(Ty::Int(Signedness::Signed)),
            len: len.clone(),
        };
        let definition = FnDef {
            name: FnName("load".to_owned()),
            params: vec![
                TypedVar::new("index", Ty::Int(Signedness::Unsigned)),
                TypedVar::new("array", array_ty.clone()),
            ],
            alloc_arrays: vec![],
            caps: vec![],
            returns: Ty::Int(Signedness::Signed),
            body: Expr {
                stmts: vec![Stmt::LetOp {
                    vars: vec![var("value")],
                    op: Op::Load {
                        array: var("array"),
                        index: var("index"),
                        len,
                    },
                    fence: false,
                }],
                tail: Tail::RetVar(var("value")),
            },
        };

        let typed = type_program(&Program {
            defs: vec![definition],
        })
        .unwrap();
        let Stmt::LetOp {
            vars,
            op: Op::Load { array, index, .. },
            ..
        } = &typed.defs[0].body.stmts[0]
        else {
            panic!("expected typed load")
        };
        assert_eq!(vars[0].ty, Ty::Int(Signedness::Signed));
        assert_eq!(array.ty, array_ty);
        assert_eq!(index.ty, Ty::Int(Signedness::Unsigned));
    }
}
