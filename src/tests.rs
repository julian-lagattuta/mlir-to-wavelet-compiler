use std::{collections::HashMap, rc::Rc};

use melior::{
    Context,
    dialect::DialectRegistry,
    ir::{BlockLike, Module, RegionLike, Value, ValueLike, operation::{OperationLike, OperationMutLike}},
    utility::register_all_dialects,
};

use super::capabilities::{
    Capability, CapabilityExpr, CapabilityOp, CapabilityType, Pattern, block_capabilities,
    capability_constants, coalesce_capabilities, coalesce_capabilities_by_array, coalesce_pair,
    compute_capabilities, find_parent_iterator, format_capabilities, generate_expr, z3_assumptions,
    z3_for_loop_viability,
};

#[test]
fn function_call_order_handles_forward_nested_repeated_and_self_calls() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
            module {
                func.func @caller(%condition: i1) {
                    scf.if %condition {
                        func.call @middle() : () -> ()
                    } else {
                        func.call @middle() : () -> ()
                    }
                    func.call @leaf() : () -> ()
                    return
                }
                func.func @middle() {
                    func.call @middle() : () -> ()
                    func.call @leaf() : () -> ()
                    return
                }
                func.func @leaf() {
                    return
                }
            }
        "#,
    )
    .unwrap();

    let functions = super::functions_in_call_order(module.body()).unwrap();
    let names: Vec<_> = functions.iter().map(super::function_to_name).collect();
    assert_eq!(names, ["leaf", "middle", "caller"]);
}

#[test]
fn function_call_order_handles_empty_and_disconnected_modules() {
    let context = test_context();
    let empty = Module::parse(&context, "module {}").unwrap();
    assert!(super::functions_in_call_order(empty.body()).unwrap().is_empty());

    let module = Module::parse(
        &context,
        r#"
            module {
                func.func @first() { return }
                func.func private @external()
                func.func @last() { return }
            }
        "#,
    )
    .unwrap();
    let functions = super::functions_in_call_order(module.body()).unwrap();
    let names: Vec<_> = functions.iter().map(super::function_to_name).collect();
    assert_eq!(names, ["first", "external", "last"]);
}

#[test]
fn function_call_order_rejects_mutual_recursion() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
            module {
                func.func @first() {
                    func.call @second() : () -> ()
                    return
                }
                func.func @second() {
                    func.call @third() : () -> ()
                    return
                }
                func.func @third() {
                    func.call @first() : () -> ()
                    return
                }
            }
        "#,
    )
    .unwrap();
    let error = super::functions_in_call_order(module.body()).unwrap_err();
    assert_eq!(error.to_string(), "mutual recursion is not supported");
}

#[test]
fn function_call_order_rejects_unknown_callees() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
            module {
                func.func @caller() {
                    func.call @caller() : () -> ()
                    return
                }
            }
        "#,
    )
    .unwrap();
    // Parsing verifies symbol references, so introduce the missing symbol afterward.
    let caller = module.body().first_operation().unwrap();
    let body = caller.first_region().unwrap().first_block().unwrap();
    let mut call = body.first_operation_mut().unwrap();
    call.set_attribute(
        "callee",
        melior::ir::attribute::FlatSymbolRefAttribute::new(&context, "missing").into(),
    );
    let error = super::functions_in_call_order(module.body()).unwrap_err();
    assert_eq!(error.to_string(), "function 'caller' calls unknown function 'missing'");
}

    fn test_context() -> Context {
    let registry = DialectRegistry::new();
    register_all_dialects(&registry);
    let context = Context::new_with_registry(&registry, false);
    for dialect in ["memref", "arith", "func", "scf"] {
        context.get_or_load_dialect(dialect);
    }
        context
    }

    #[test]
    fn value_to_wavelet_ty_handles_integer_signedness_bool_and_index() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(
                        %signless: i32,
                        %signed: si32,
                        %unsigned: ui32,
                        %flag: i1,
                        %index: index
                    ) {
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let ty = |index| {
            let value: Value<'_, '_> = block.argument(index).unwrap().into();
            super::value_to_wavelet_ty(&value)
        };

        assert_eq!(
            ty(0),
            wavelet_elab::Ty::Int(
                wavelet_elab::ir::Signedness::Signed
            )
        );
        assert_eq!(
            ty(1),
            wavelet_elab::Ty::Int(
                wavelet_elab::ir::Signedness::Signed
            )
        );
        assert_eq!(
            ty(2),
            wavelet_elab::Ty::Int(
                wavelet_elab::ir::Signedness::Unsigned
            )
        );
        assert_eq!(ty(3), wavelet_elab::Ty::Bool);
        assert_eq!(
            ty(4),
            wavelet_elab::Ty::Int(
                wavelet_elab::ir::Signedness::Signed
            )
        );
    }

    #[test]
    fn function_to_name_removes_surrounding_quotation_marks() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @example_function() {
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();

        assert_eq!(super::function_to_name(&function), "example_function");
    }

    #[test]
    fn value_to_wavelet_ty_maps_static_memrefs_to_mutable_arrays() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(%array: memref<32xui32>) {
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let array: Value<'_, '_> = block.argument(0).unwrap().into();

        assert_eq!(
            super::value_to_wavelet_ty(&array),
            wavelet_elab::Ty::RefUniq {
                elem: Box::new(wavelet_elab::Ty::Int(
                    wavelet_elab::ir::Signedness::Unsigned
                )),
                len: wavelet_elab::ir::ArrayLen::Const(32),
            }
        );
    }

    #[test]
    #[should_panic(expected = "Wavelet only supports one-dimensional arrays")]
    fn value_to_wavelet_ty_rejects_multidimensional_memrefs() {
        let context = test_context();
        let module = Module::parse(
            &context,
            "module { func.func @test(%array: memref<4x8xi32>) { return } }",
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let array: Value<'_, '_> = block.argument(0).unwrap().into();

        super::value_to_wavelet_ty(&array);
    }

    #[test]
    #[should_panic(expected = "Wavelet does not support dynamically sized arrays")]
    fn value_to_wavelet_ty_rejects_dynamic_memrefs() {
        let context = test_context();
        let module = Module::parse(
            &context,
            "module { func.func @test(%array: memref<?xi32>) { return } }",
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let array: Value<'_, '_> = block.argument(0).unwrap().into();

        super::value_to_wavelet_ty(&array);
    }

    #[test]
    fn operation_to_wavelet_builds_comparison_and_boolean_xor_statements() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(%lhs: i32, %rhs: i32, %flag: i1) {
                        %greater = arith.cmpi sgt, %lhs, %rhs : i32
                        %true = arith.constant true
                        %not = arith.xori %flag, %true : i1
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let greater = block.first_operation().unwrap();
        let not = greater.next_in_block().unwrap().next_in_block().unwrap();

        let wavelet_elab::Stmt::LetOp { vars, op, fence } =
            super::operation_to_wavelet(greater, "arith.cmpi").unwrap().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(op, wavelet_elab::Op::SignedLessThan);
        assert_eq!(vars.len(), 3);
        assert_eq!(
            vars[0],
            wavelet_elab::UntypedVar(super::value_to_name(&greater.operand(1).unwrap()))
        );
        assert_eq!(
            vars[1],
            wavelet_elab::UntypedVar(super::value_to_name(&greater.operand(0).unwrap()))
        );
        assert_eq!(
            vars[2],
            wavelet_elab::UntypedVar(super::value_to_name(
                &greater.result(0).unwrap().into()
            ))
        );
        assert!(!fence);

        let wavelet_elab::Stmt::LetOp { vars, op, fence } =
            super::operation_to_wavelet(not, "arith.xori").unwrap().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(op, wavelet_elab::Op::NotEqual);
        assert_eq!(vars.len(), 3);
        assert_eq!(
            vars[0],
            wavelet_elab::UntypedVar(super::value_to_name(&not.operand(0).unwrap()))
        );
        assert_eq!(
            vars[1],
            wavelet_elab::UntypedVar(super::value_to_name(&not.operand(1).unwrap()))
        );
        assert_eq!(
            vars[2],
            wavelet_elab::UntypedVar(super::value_to_name(&not.result(0).unwrap().into()))
        );
        assert!(!fence);
    }

    #[test]
    fn operation_to_wavelet_supports_exportable_arithmetic_operations() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(%x: i32, %y: i32, %a: i1, %b: i1) {
                        %add = arith.addi %x, %y : i32
                        %sub = arith.subi %x, %y : i32
                        %mul = arith.muli %x, %y : i32
                        %sdiv = arith.divsi %x, %y : i32
                        %udiv = arith.divui %x, %y : i32
                        %bitand = arith.andi %x, %y : i32
                        %bitor = arith.ori %x, %y : i32
                        %bitxor = arith.xori %x, %y : i32
                        %shl = arith.shli %x, %y : i32
                        %ashr = arith.shrsi %x, %y : i32
                        %lshr = arith.shrui %x, %y : i32
                        %and = arith.andi %a, %b : i1
                        %or = arith.ori %a, %b : i1
                        %xor = arith.xori %a, %b : i1
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let expected = [
            wavelet_elab::Op::Add,
            wavelet_elab::Op::Sub,
            wavelet_elab::Op::Mul,
            wavelet_elab::Op::Sdiv,
            wavelet_elab::Op::Udiv,
            wavelet_elab::Op::BitAnd,
            wavelet_elab::Op::BitOr,
            wavelet_elab::Op::BitXor,
            wavelet_elab::Op::Shl,
            wavelet_elab::Op::Ashr,
            wavelet_elab::Op::Lshr,
            wavelet_elab::Op::And,
            wavelet_elab::Op::Or,
            wavelet_elab::Op::NotEqual,
        ];

        let mut operation = block.first_operation();
        for expected_op in expected {
            let current = operation.unwrap();
            let identifier = current.name();
            let name = identifier.as_string_ref().as_str().unwrap();
            let wavelet_elab::Stmt::LetOp { vars, op, fence } =
                super::operation_to_wavelet(current, name).unwrap().unwrap()
            else {
                unreachable!()
            };
            assert_eq!(op, expected_op);
            assert_eq!(vars.len(), 3);
            assert!(!fence);
            operation = current.next_in_block();
        }
    }

    #[test]
    fn operation_to_wavelet_builds_integer_and_boolean_constants() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test() {
                        %integer = arith.constant -7 : i32
                        %boolean = arith.constant true
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let integer = block.first_operation().unwrap();
        let boolean = integer.next_in_block().unwrap();

        let wavelet_elab::Stmt::LetVal { val, fence, .. } =
            super::operation_to_wavelet(integer, "arith.constant").unwrap().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(val, wavelet_elab::Val::Int(-7));
        assert!(!fence);

        let wavelet_elab::Stmt::LetVal { val, fence, .. } =
            super::operation_to_wavelet(boolean, "arith.constant").unwrap().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(val, wavelet_elab::Val::Bool(true));
        assert!(!fence);
    }

    #[test]
    fn operation_to_wavelet_builds_memref_load_and_store_statements() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(%array: memref<16xi32>, %index: index, %value: i32) {
                        %loaded = memref.load %array[%index] : memref<16xi32>
                        memref.store %value, %array[%index] : memref<16xi32>
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let load = block.first_operation().unwrap();
        let store = load.next_in_block().unwrap();

        let wavelet_elab::Stmt::LetOp { vars, op, fence } =
            super::operation_to_wavelet(load, "memref.load").unwrap().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(
            vars,
            vec![wavelet_elab::UntypedVar(super::value_to_name(
                &load.result(0).unwrap().into()
            ))]
        );
        let wavelet_elab::Op::Load { array, index, len } = op else {
            unreachable!()
        };
        assert_eq!(array, wavelet_elab::UntypedVar(super::value_to_name(&load.operand(0).unwrap())));
        assert_eq!(index, wavelet_elab::UntypedVar(super::value_to_name(&load.operand(1).unwrap())));
        assert_eq!(len, wavelet_elab::ir::ArrayLen::Const(16));
        assert!(!fence);

        let wavelet_elab::Stmt::LetOp { vars, op, fence } =
            super::operation_to_wavelet(store, "memref.store").unwrap().unwrap()
        else {
            unreachable!()
        };
        assert!(vars.is_empty());
        let wavelet_elab::Op::Store {
            array,
            index,
            value,
            len,
        } = op
        else {
            unreachable!()
        };
        assert_eq!(array, wavelet_elab::UntypedVar(super::value_to_name(&store.operand(1).unwrap())));
        assert_eq!(index, wavelet_elab::UntypedVar(super::value_to_name(&store.operand(2).unwrap())));
        assert_eq!(value, wavelet_elab::UntypedVar(super::value_to_name(&store.operand(0).unwrap())));
        assert_eq!(len, wavelet_elab::ir::ArrayLen::Const(16));
        assert!(!fence);
    }

    #[test]
    fn operation_to_wavelet_treats_distinct_objects_as_a_noop() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(%array: memref<16xi32>) {
                        %distinct = memref.distinct_objects %array : memref<16xi32>
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let distinct_objects = block.first_operation().unwrap();

        assert!(
            super::operation_to_wavelet(distinct_objects, "memref.distinct_objects").is_none()
        );
    }

    #[test]
    #[should_panic(expected = "unsupported MLIR operation: arith.negf")]
    fn operation_to_wavelet_panics_for_unsupported_operations() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @test(%value: f32) {
                        %negated = arith.negf %value : f32
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let function = module.body().first_operation().unwrap();
        let block = function.first_region().unwrap().first_block().unwrap();
        let unsupported = block.first_operation().unwrap();

        super::operation_to_wavelet(unsupported, "arith.negf");
    }

    #[test]
    fn operation_to_wavelet_builds_function_calls() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func private @callee(memref<4xi32>, i32) -> i32
                    func.func @caller(%array: memref<4xi32>, %value: i32) -> i32 {
                        %result = func.call @callee(%array, %value) : (memref<4xi32>, i32) -> i32
                        return %result : i32
                    }
                }
            "#,
        )
        .unwrap();
        let caller = module.body().first_operation().unwrap().next_in_block().unwrap();
        let block = caller.first_region().unwrap().first_block().unwrap();
        let call = block.first_operation().unwrap();

        let wavelet_elab::Stmt::LetCall {
            vars,
            func,
            args,
            fence,
        } = super::operation_to_wavelet(call, "func.call").unwrap().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(func, wavelet_elab::FnName("callee".to_string()));
        assert_eq!(
            vars,
            vec![wavelet_elab::UntypedVar(super::value_to_name(
                &call.result(0).unwrap().into()
            ))]
        );
        assert_eq!(
            args,
            vec![
                wavelet_elab::UntypedVar(super::value_to_name(&call.operand(1).unwrap())),
                wavelet_elab::UntypedVar(super::value_to_name(&call.operand(0).unwrap())),
            ]
        );
        assert!(!fence);
    }

    #[test]
    fn block_to_wavelet_builds_value_and_unit_returns() {
        let context = test_context();
        let module = Module::parse(
            &context,
            r#"
                module {
                    func.func @value_return(%value: i32) -> i32 {
                        return %value : i32
                    }
                    func.func @unit_return() {
                        return
                    }
                }
            "#,
        )
        .unwrap();
        let value_function = module.body().first_operation().unwrap();
        let unit_function = value_function.next_in_block().unwrap();
        let value_block = value_function
            .first_region()
            .unwrap()
            .first_block()
            .unwrap();
        let unit_block = unit_function
            .first_region()
            .unwrap()
            .first_block()
            .unwrap();

        let mut program = wavelet_elab::Program::new();
        let mut capability_map = HashMap::new();
        let value_expr = super::block_to_wavelet(
            value_block,
            &mut program,
            None,
            &mut capability_map,
        );
        let wavelet_elab::Tail::RetVar(value) = value_expr.tail
        else {
            unreachable!()
        };
        assert_eq!(
            value,
            wavelet_elab::UntypedVar(super::value_to_name(
                &value_block.first_operation().unwrap().operand(0).unwrap()
            ))
        );

        let unit_expr = super::block_to_wavelet(
            unit_block,
            &mut program,
            None,
            &mut capability_map,
        );
        let wavelet_elab::Tail::RetVar(value) = unit_expr.tail
        else {
            unreachable!()
        };
        assert_eq!(value, wavelet_elab::UntypedVar("_unit_ret".to_string()));
        assert!(matches!(
            unit_expr.stmts.as_slice(),
            [wavelet_elab::Stmt::LetVal {
                val: wavelet_elab::Val::Unit,
                ..
            }]
        ));
    }

    fn bin_op<'c, 'a>(
    operation: CapabilityOp,
    lhs: CapabilityExpr<'c, 'a>,
    rhs: CapabilityExpr<'c, 'a>,
) -> CapabilityExpr<'c, 'a> {
    CapabilityExpr::BinOp {
        operation,
        operands: (Rc::new(lhs), Rc::new(rhs)),
    }
}

#[test]
fn constant_propagate_evaluates_constant_trees() {
    let expression = bin_op(
        CapabilityOp::Mult,
        bin_op(
            CapabilityOp::Add,
            CapabilityExpr::Constant(2),
            CapabilityExpr::Constant(3),
        ),
        bin_op(
            CapabilityOp::Sub,
            CapabilityExpr::Constant(10),
            CapabilityExpr::Constant(4),
        ),
    );

    assert_eq!(expression.constant_propagate(), Some(30));
    assert!(matches!(
        expression.simplified(),
        CapabilityExpr::Constant(30)
    ));
    assert_eq!(expression.to_string(), "30");

    let overflow = bin_op(
        CapabilityOp::Add,
        CapabilityExpr::Constant(i64::MAX),
        CapabilityExpr::Constant(1),
    );
    assert_eq!(overflow.constant_propagate(), None);
}

#[test]
fn capability_constants_folds_constant_values_in_the_capability_map() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @test(%array: memref<10xi32>) {
                        %c2 = arith.constant 2 : index
                        %c3 = arith.constant 3 : index
                        %sum = arith.addi %c2, %c3 : index
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let block = function.first_region().unwrap().first_block().unwrap();
    let array: Value<'_, '_> = block.argument(0).unwrap().into();
    let sum: Value<'_, '_> = block
        .first_operation()
        .unwrap()
        .next_in_block()
        .unwrap()
        .next_in_block()
        .unwrap()
        .result(0)
        .unwrap()
        .into();
    let mut capability_map = HashMap::from([(
        function.to_raw().ptr,
        vec![Capability {
            array,
            capability_type: CapabilityType::Shrd,
            capability_expr: Some((
                CapabilityExpr::Blackbox {
                    value: sum,
                    signedness: wavelet_elab::ir::Signedness::Signed,
                },
                bin_op(
                    CapabilityOp::Add,
                    CapabilityExpr::Blackbox {
                        value: sum,
                        signedness: wavelet_elab::ir::Signedness::Signed,
                    },
                    CapabilityExpr::Constant(1),
                ),
            )),
        }],
    )]);

    capability_constants(&mut capability_map);

    let (start, end) = capability_map[&function.to_raw().ptr][0]
        .capability_expr
        .as_ref()
        .unwrap();
    assert_eq!(start.constant_propagate(), Some(5));
    assert_eq!(end.constant_propagate(), Some(6));
}

#[test]
fn partition_captured_values_materializes_constants_instead_of_parameters() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @test(%dynamic: index) {
                        %c2 = arith.constant 2 : index
                        %c3 = arith.constant 3 : index
                        %sum = arith.addi %c2, %c3 : index
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let block = function.first_region().unwrap().first_block().unwrap();
    let dynamic: Value<'_, '_> = block.argument(0).unwrap().into();
    let c2: Value<'_, '_> = block.first_operation().unwrap().result(0).unwrap().into();
    let sum: Value<'_, '_> = block
        .first_operation()
        .unwrap()
        .next_in_block()
        .unwrap()
        .next_in_block()
        .unwrap()
        .result(0)
        .unwrap()
        .into();

    let (parameters, constants) = super::partition_captured_values(&[dynamic, c2, sum]);

    assert_eq!(parameters.len(), 1);
    assert_eq!(parameters[0].name, super::value_to_name(&dynamic));
    assert!(matches!(
        constants.as_slice(),
        [
            wavelet_elab::Stmt::LetVal {
                val: wavelet_elab::Val::Int(2),
                ..
            },
            wavelet_elab::Stmt::LetVal {
                val: wavelet_elab::Val::Int(5),
                ..
            }
        ]
    ));
}

#[test]
fn promote_replaces_variables_and_only_selected_blackboxes() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @test(%end: index, %other: index) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        scf.for %i = %c0 to %end step %c1 {
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let end_value: Value<'_, '_> = body.argument(0).unwrap().into();
    let other_value: Value<'_, '_> = body.argument(1).unwrap().into();
    let mut current = body.first_operation().unwrap();
    let for_loop = loop {
        if current.name().as_string_ref().as_str().unwrap() == "scf.for" {
            break current;
        }
        current = current.next_in_block().unwrap();
    };
    let iterator: Value<'_, '_> = for_loop
        .first_region()
        .unwrap()
        .first_block()
        .unwrap()
        .argument(0)
        .unwrap()
        .into();

    let expression = bin_op(
        CapabilityOp::Add,
        CapabilityExpr::Variable {
            value: iterator,
            signedness: wavelet_elab::ir::Signedness::Signed,
        },
        bin_op(
            CapabilityOp::Add,
            CapabilityExpr::Blackbox {
                value: iterator,
                signedness: wavelet_elab::ir::Signedness::Signed,
            },
            CapabilityExpr::Blackbox {
                value: other_value,
                signedness: wavelet_elab::ir::Signedness::Signed,
            },
        ),
    );
    let expression = expression
        .promote(&CapabilityExpr::Constant(7), Some(for_loop))
        .unwrap();

    let CapabilityExpr::BinOp { operands, .. } = &expression else {
        panic!("promotion should preserve the outer binary operation");
    };
    assert!(matches!(operands.0.as_ref(), CapabilityExpr::Constant(7)));
    let CapabilityExpr::BinOp { operands, .. } = operands.1.as_ref() else {
        panic!("promotion should preserve the nested binary operation");
    };
    assert!(
        matches!(operands.0.as_ref(), CapabilityExpr::Variable { value, .. }
            if value.to_raw().ptr == iterator.to_raw().ptr)
    );
    assert!(
        matches!(operands.1.as_ref(), CapabilityExpr::Blackbox { value, .. }
            if value.to_raw().ptr == other_value.to_raw().ptr)
    );
    assert_eq!(expression.to_string(), "7 + i + arg1");

    let simple_symbolic = bin_op(
        CapabilityOp::Add,
        CapabilityExpr::Variable {
            value: iterator,
            signedness: wavelet_elab::ir::Signedness::Signed,
        },
        CapabilityExpr::Constant(5),
    );
    assert_eq!(simple_symbolic.to_string(), "i + 5");

    let no_blackbox_promotion = CapabilityExpr::Blackbox {
        value: end_value,
        signedness: wavelet_elab::ir::Signedness::Signed,
    }
        .promote(&CapabilityExpr::Constant(9), None)
        .unwrap();
    assert!(matches!(no_blackbox_promotion, CapabilityExpr::Blackbox { .. }));
}

#[test]
fn generate_expr_classifies_values_relative_to_target_loop() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @test(%end: index, %initial: index) -> index {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c2 = arith.constant 2 : index
                        %c3 = arith.constant 3 : index
                        %folded = arith.addi %c2, %c3 : index
                        %outside_math = arith.addi %end, %c1 : index
                        %outside = arith.index_cast %end : index to i64
                        %result = scf.for %i = %c0 to %end step %c1
                            iter_args(%carried = %initial) -> index {
                            %supported = arith.addi %i, %c1 : index
                            %inside = arith.index_cast %i : index to i64
                            %next = arith.addi %carried, %c1 : index
                            scf.yield %next : index
                        }
                        return %result : index
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let end_value: Value<'_, '_> = body.argument(0).unwrap().into();
    let mut current = body.first_operation().unwrap();
    let mut add_results = vec![];
    let (outside, for_loop) = loop {
        let ident = current.name();
        let name = ident.as_string_ref().as_str().unwrap();
        if name == "arith.addi" {
            add_results.push(current.result(0).unwrap().into());
        } else if name == "arith.index_cast" {
            let outside = current.result(0).unwrap().into();
            current = current.next_in_block().unwrap();
            while current.name().as_string_ref().as_str().unwrap() != "scf.for" {
                current = current.next_in_block().unwrap();
            }
            break (outside, current);
        }
        current = current.next_in_block().unwrap();
    };
    let folded = add_results[0];
    let outside_math = add_results[1];
    let loop_body = for_loop.first_region().unwrap().first_block().unwrap();
    let iterator: Value<'_, '_> = loop_body.argument(0).unwrap().into();
    let carried: Value<'_, '_> = loop_body.argument(1).unwrap().into();
    let supported: Value<'_, '_> = loop_body
        .first_operation()
        .unwrap()
        .result(0)
        .unwrap()
        .into();
    let inside: Value<'_, '_> = loop_body
        .first_operation()
        .unwrap()
        .next_in_block()
        .unwrap()
        .result(0)
        .unwrap()
        .into();

    assert!(matches!(
        generate_expr(end_value, Some(for_loop)),
        Some(CapabilityExpr::Blackbox { value, signedness })
            if value.to_raw().ptr == end_value.to_raw().ptr
                && signedness == wavelet_elab::ir::Signedness::Signed
    ));
    assert!(matches!(
        generate_expr(iterator, Some(for_loop)),
        Some(CapabilityExpr::Variable { value, signedness })
            if value.to_raw().ptr == iterator.to_raw().ptr
                && signedness == wavelet_elab::ir::Signedness::Signed
    ));
    assert!(generate_expr(carried, Some(for_loop)).is_none());
    assert_eq!(
        generate_expr(folded, Some(for_loop))
            .unwrap()
            .constant_propagate(),
        Some(5)
    );
    assert!(matches!(
        generate_expr(outside_math, Some(for_loop)),
        Some(CapabilityExpr::Blackbox { value, signedness })
            if value.to_raw().ptr == outside_math.to_raw().ptr
                && signedness == wavelet_elab::ir::Signedness::Signed
    ));
    assert!(matches!(
        generate_expr(outside, Some(for_loop)),
        Some(CapabilityExpr::Blackbox { value, signedness })
            if value.to_raw().ptr == outside.to_raw().ptr
                && signedness == wavelet_elab::ir::Signedness::Signed
    ));
    assert!(matches!(
        generate_expr(supported, Some(for_loop)),
        Some(CapabilityExpr::BinOp { .. })
    ));
    assert!(generate_expr(inside, Some(for_loop)).is_none());
    assert!(
        CapabilityExpr::Blackbox {
            value: inside,
            signedness: wavelet_elab::ir::Signedness::Signed,
        }
            .promote(&CapabilityExpr::Constant(0), Some(for_loop))
            .is_none()
    );
}

#[test]
fn generate_expr_uses_scf_for_unsigned_keyword_for_variable_signedness() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @test(%lower: i32, %upper: i32, %step: i32, %outside: ui32) {
                        scf.for unsigned %i = %lower to %upper step %step : i32 {
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let lower: Value<'_, '_> = body.argument(0).unwrap().into();
    let outside: Value<'_, '_> = body.argument(3).unwrap().into();
    let for_loop = body.first_operation().unwrap();
    let iterator: Value<'_, '_> = for_loop
        .first_region()
        .unwrap()
        .first_block()
        .unwrap()
        .argument(0)
        .unwrap()
        .into();

    assert!(matches!(
        generate_expr(iterator, Some(for_loop)),
        Some(CapabilityExpr::Variable { value, signedness })
            if value.to_raw().ptr == iterator.to_raw().ptr
                && signedness == wavelet_elab::ir::Signedness::Unsigned
    ));
    assert!(matches!(
        generate_expr(lower, Some(for_loop)),
        Some(CapabilityExpr::Blackbox { value, signedness })
            if value.to_raw().ptr == lower.to_raw().ptr
                && signedness == wavelet_elab::ir::Signedness::Signed
    ));
    assert!(matches!(
        generate_expr(outside, Some(for_loop)),
        Some(CapabilityExpr::Blackbox { value, signedness })
            if value.to_raw().ptr == outside.to_raw().ptr
                && signedness == wavelet_elab::ir::Signedness::Signed
    ));
}

#[test]
#[should_panic(expected = "unsigned for loops are not supported")]
fn module_to_wavelet_rejects_unsigned_for_loops() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
            module {
                func.func @test(%lower: i32, %upper: i32, %step: i32) {
                    scf.for unsigned %i = %lower to %upper step %step : i32 {
                        scf.yield
                    }
                    return
                }
            }
        "#,
    )
    .unwrap();

    let _ = super::module_to_wavelet(module);
}

#[test]
fn z3_detects_increasing_decreasing_and_poison_patterns() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @test(%end: index, %factor: index) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        scf.for %i = %c0 to %end step %c1 {
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let end_value: Value<'_, '_> = body.argument(0).unwrap().into();
    let factor_value: Value<'_, '_> = body.argument(1).unwrap().into();
    let mut current = body.first_operation().unwrap();
    let for_loop = loop {
        if current.name().as_string_ref().as_str().unwrap() == "scf.for" {
            break current;
        }
        current = current.next_in_block().unwrap();
    };
    let iterator: Value<'_, '_> = for_loop
        .first_region()
        .unwrap()
        .first_block()
        .unwrap()
        .argument(0)
        .unwrap()
        .into();

    let unsigned_variable = || CapabilityExpr::Variable {
        value: iterator,
        signedness: wavelet_elab::ir::Signedness::Unsigned,
    };
    let increasing = unsigned_variable();
    assert_eq!(z3_assumptions(&increasing).len(), 1);
    assert_eq!(
        z3_for_loop_viability(&increasing, &increasing, &end_value),
        Pattern::Increasing
    );

    let decreasing = bin_op(
        CapabilityOp::Sub,
        CapabilityExpr::Constant(0),
        unsigned_variable(),
    );
    assert_eq!(
        z3_for_loop_viability(&decreasing, &decreasing, &end_value),
        Pattern::Decreasing
    );

    let square = bin_op(
        CapabilityOp::Mult,
        unsigned_variable(),
        unsigned_variable(),
    );
    assert_eq!(
        z3_for_loop_viability(&square, &square, &end_value),
        Pattern::Increasing
    );

    let signed_square = bin_op(
        CapabilityOp::Mult,
        CapabilityExpr::Variable {
            value: iterator,
            signedness: wavelet_elab::ir::Signedness::Signed,
        },
        CapabilityExpr::Variable {
            value: iterator,
            signedness: wavelet_elab::ir::Signedness::Signed,
        },
    );
    assert_eq!(
        z3_for_loop_viability(&signed_square, &signed_square, &end_value),
        Pattern::Poison
    );
    assert!(z3_assumptions(&signed_square).is_empty());

    let shifted = bin_op(
        CapabilityOp::Sub,
        unsigned_variable(),
        CapabilityExpr::Constant(1),
    );
    let non_monotonic = bin_op(CapabilityOp::Mult, shifted.clone(), shifted);
    assert_eq!(
        z3_for_loop_viability(&non_monotonic, &non_monotonic, &end_value),
        Pattern::Poison
    );

    let parameterized = bin_op(
        CapabilityOp::Mult,
        unsigned_variable(),
        CapabilityExpr::Blackbox {
            value: factor_value,
            signedness: wavelet_elab::ir::Signedness::Signed,
        },
    );
    assert_eq!(
        z3_for_loop_viability(&parameterized, &parameterized, &end_value),
        Pattern::Poison
    );
}

#[test]
fn coalesce_pair_subtracts_unique_interval_from_shared_interval() {
    let context = test_context();
    let module = Module::parse(
        &context,
        "module { func.func @test(%array: memref<10xi32>) { return } }",
    )
    .unwrap();
    let array: Value<'_, '_> = module
        .body()
        .first_operation()
        .unwrap()
        .first_region()
        .unwrap()
        .first_block()
        .unwrap()
        .argument(0)
        .unwrap()
        .into();

    let capability = |capability_type, bounds: Option<(i64, i64)>| Capability {
        array,
        capability_type,
        capability_expr: bounds.map(|(start, end)| {
            (
                CapabilityExpr::Constant(start),
                CapabilityExpr::Constant(end),
            )
        }),
    };
    let bounds = |capability: Option<Capability<'_, '_>>| {
        capability.map(|capability| {
            let (start, end) = capability.capability_expr.unwrap();
            (
                start.constant_propagate().unwrap(),
                end.constant_propagate().unwrap(),
            )
        })
    };

    let run = |shrd_bounds, uniq_bounds| {
        let shrd = capability(CapabilityType::Shrd, shrd_bounds);
        let mut uniq = capability(CapabilityType::Uniq, uniq_bounds);
        let (first, second, generated_uniq) = coalesce_pair(shrd, &mut uniq);
        (bounds(first), bounds(second), bounds(generated_uniq))
    };

    assert_eq!(
        run(Some((0, 2)), Some((5, 7))),
        (Some((0, 2)), None, None)
    );
    assert_eq!(run(Some((2, 4)), Some((0, 6))), (None, None, None));
    assert_eq!(
        run(Some((1, 5)), Some((0, 2))),
        (Some((3, 5)), None, None)
    );
    assert_eq!(
        run(Some((1, 5)), Some((4, 8))),
        (Some((1, 3)), None, None)
    );
    assert_eq!(
        run(Some((1, 8)), Some((3, 5))),
        (Some((1, 2)), Some((6, 8)), None)
    );
    assert_eq!(
        run(None, Some((3, 5))),
        (Some((0, 2)), Some((6, 9)), None)
    );
    assert_eq!(run(Some((3, 5)), None), (None, None, None));
    assert_eq!(run(Some((5, 4)), Some((0, 1))), (None, None, None));
    assert_eq!(run(Some((2, 4)), Some((2, 4))), (None, None, None));
    assert_eq!(
        run(Some((1, 5)), Some((5, 8))),
        (Some((1, 4)), None, None)
    );
    assert_eq!(
        run(Some((0, 1)), Some((5, 4))),
        (Some((0, 1)), None, None)
    );
}

#[test]
fn coalesce_capabilities_by_array_applies_each_unique_to_remaining_shared() {
    let context = test_context();
    let module = Module::parse(
        &context,
        "module { func.func @test(%array: memref<10xi32>, %x2: ui32, %y2: ui32) { return } }",
    )
    .unwrap();
    let block = module
        .body()
        .first_operation()
        .unwrap()
        .first_region()
        .unwrap()
        .first_block()
        .unwrap();
    let array: Value<'_, '_> = block.argument(0).unwrap().into();
    let x2: Value<'_, '_> = block.argument(1).unwrap().into();
    let y2: Value<'_, '_> = block.argument(2).unwrap().into();
    let capability = |capability_type, start, end| Capability {
        array,
        capability_type,
        capability_expr: Some((
            CapabilityExpr::Constant(start),
            CapabilityExpr::Constant(end),
        )),
    };

    let capabilities = coalesce_capabilities_by_array(vec![
        capability(CapabilityType::Shrd, 0, 9),
        capability(CapabilityType::Uniq, 2, 3),
        capability(CapabilityType::Uniq, 6, 7),
    ]);
    let bounds = |capability: &Capability<'_, '_>| {
        let (start, end) = capability.capability_expr.as_ref().unwrap();
        (
            start.constant_propagate().unwrap(),
            end.constant_propagate().unwrap(),
        )
    };
    let uniq_bounds = capabilities
        .iter()
        .filter(|capability| capability.capability_type == CapabilityType::Uniq)
        .map(bounds)
        .collect::<Vec<_>>();
    let shrd_bounds = capabilities
        .iter()
        .filter(|capability| capability.capability_type == CapabilityType::Shrd)
        .map(bounds)
        .collect::<Vec<_>>();

    assert_eq!(uniq_bounds, vec![(2, 3), (6, 7)]);
    assert_eq!(shrd_bounds, vec![(0, 1), (4, 5), (8, 9)]);

    let x_end = bin_op(
        CapabilityOp::Add,
        CapabilityExpr::Blackbox {
            value: x2,
            signedness: wavelet_elab::ir::Signedness::Unsigned,
        },
        CapabilityExpr::Constant(2),
    );
    let y_end = bin_op(
        CapabilityOp::Add,
        CapabilityExpr::Blackbox {
            value: y2,
            signedness: wavelet_elab::ir::Signedness::Unsigned,
        },
        CapabilityExpr::Constant(2),
    );
    let capabilities = coalesce_capabilities_by_array(vec![
        Capability {
            array,
            capability_type: CapabilityType::Shrd,
            capability_expr: Some((CapabilityExpr::Constant(0), y_end)),
        },
        Capability {
            array,
            capability_type: CapabilityType::Uniq,
            capability_expr: Some((CapabilityExpr::Constant(2), x_end)),
        },
    ]);
    let uniq_capabilities = capabilities
        .iter()
        .filter(|capability| capability.capability_type == CapabilityType::Uniq)
        .collect::<Vec<_>>();
    let shrd_capabilities = capabilities
        .iter()
        .filter(|capability| capability.capability_type == CapabilityType::Shrd)
        .collect::<Vec<_>>();

    assert_eq!(uniq_capabilities.len(), 2);
    assert_eq!(shrd_capabilities.len(), 1);
    assert_eq!(bounds(shrd_capabilities[0]), (0, 1));
    let (generated_start, generated_end) = uniq_capabilities[1]
        .capability_expr
        .as_ref()
        .unwrap();
    assert_eq!(generated_start.to_string(), "arg1 + 3");
    assert_eq!(generated_end.to_string(), "arg2 + 2");

    let shrd = Capability {
        array,
        capability_type: CapabilityType::Shrd,
        capability_expr: Some((
            CapabilityExpr::Blackbox {
                value: x2,
                signedness: wavelet_elab::ir::Signedness::Unsigned,
            },
            CapabilityExpr::Constant(9),
        )),
    };
    let mut uniq = Capability {
        array,
        capability_type: CapabilityType::Uniq,
        capability_expr: Some((
            CapabilityExpr::Blackbox {
                value: y2,
                signedness: wavelet_elab::ir::Signedness::Unsigned,
            },
            CapabilityExpr::Constant(9),
        )),
    };
    let (first_shrd, second_shrd, generated_uniq) = coalesce_pair(shrd, &mut uniq);
    assert!(first_shrd.is_none());
    assert!(second_shrd.is_none());
    let generated_uniq = generated_uniq.unwrap();
    assert_eq!(generated_uniq.capability_type, CapabilityType::Uniq);
    let (generated_start, generated_end) = generated_uniq.capability_expr.unwrap();
    assert_eq!(generated_start.to_string(), "arg1");
    assert_eq!(generated_end.constant_propagate(), Some(9));

    let iteration = CapabilityExpr::Blackbox {
        value: x2,
        signedness: wavelet_elab::ir::Signedness::Signed,
    };
    let shrd = Capability {
        array,
        capability_type: CapabilityType::Shrd,
        capability_expr: Some((iteration.clone(), CapabilityExpr::Constant(3))),
    };
    let mut uniq = Capability {
        array,
        capability_type: CapabilityType::Uniq,
        capability_expr: Some((
            bin_op(
                CapabilityOp::Add,
                iteration,
                CapabilityExpr::Constant(4),
            ),
            CapabilityExpr::Constant(7),
        )),
    };
    let (coalesced_shrd, second_shrd, generated_uniq) = coalesce_pair(shrd, &mut uniq);
    let (coalesced_start, coalesced_end) = coalesced_shrd
        .unwrap()
        .capability_expr
        .unwrap();
    assert_eq!(coalesced_start.to_string(), "arg1");
    assert_eq!(coalesced_end.to_string(), "arg1 + 4 - 1");
    assert!(second_shrd.is_none());
    assert!(generated_uniq.is_none());

    let iteration = CapabilityExpr::Blackbox {
        value: x2,
        signedness: wavelet_elab::ir::Signedness::Signed,
    };
    let row_start = bin_op(
        CapabilityOp::Mult,
        iteration,
        CapabilityExpr::Constant(4),
    );
    let shrd = Capability {
        array,
        capability_type: CapabilityType::Shrd,
        capability_expr: Some((row_start.clone(), CapabilityExpr::Constant(11))),
    };
    let mut uniq = Capability {
        array,
        capability_type: CapabilityType::Uniq,
        capability_expr: Some((
            bin_op(
                CapabilityOp::Add,
                row_start,
                CapabilityExpr::Constant(4),
            ),
            CapabilityExpr::Constant(15),
        )),
    };
    let (coalesced_shrd, second_shrd, generated_uniq) = coalesce_pair(shrd, &mut uniq);
    let (coalesced_start, coalesced_end) = coalesced_shrd
        .unwrap()
        .capability_expr
        .unwrap();
    assert_eq!(coalesced_start.to_string(), "arg1 * 4");
    assert_eq!(coalesced_end.to_string(), "arg1 * 4 + 4 - 1");
    assert!(second_shrd.is_none());
    assert!(generated_uniq.is_none());

    let capabilities = coalesce_capabilities_by_array(vec![
        capability(CapabilityType::Shrd, 5, 4),
        capability(CapabilityType::Uniq, 7, 6),
    ]);
    assert!(capabilities.is_empty());
}

#[test]
fn coalesce_capabilities_processes_each_array_independently() {
    let context = test_context();
    let module = Module::parse(
        &context,
        "module { func.func @test(%a: memref<10xi32>, %b: memref<10xi32>) { return } }",
    )
    .unwrap();
    let block = module
        .body()
        .first_operation()
        .unwrap()
        .first_region()
        .unwrap()
        .first_block()
        .unwrap();
    let a: Value<'_, '_> = block.argument(0).unwrap().into();
    let b: Value<'_, '_> = block.argument(1).unwrap().into();
    let capability = |array, capability_type, start, end| Capability {
        array,
        capability_type,
        capability_expr: Some((
            CapabilityExpr::Constant(start),
            CapabilityExpr::Constant(end),
        )),
    };

    let capabilities = coalesce_capabilities(vec![
        capability(a, CapabilityType::Shrd, 0, 5),
        capability(b, CapabilityType::Shrd, 0, 5),
        capability(a, CapabilityType::Uniq, 2, 3),
        capability(b, CapabilityType::Uniq, 4, 5),
    ]);

    assert_eq!(
        format_capabilities(&capabilities),
        "arg0: uniq @ 2..3, arg0: shrd @ 0..1, arg0: shrd @ 4..5, arg1: uniq @ 4..5, arg1: shrd @ 0..3"
    );
}

#[test]
fn compute_capabilities_coalesces_if_and_function_capabilities() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
            module {
                func.func @test(%array: memref<4xi32>, %condition: i1, %value: i32) {
                    %c0 = arith.constant 0 : index
                    scf.if %condition {
                        %loaded = memref.load %array[%c0] : memref<4xi32>
                        scf.yield
                    } else {
                        memref.store %value, %array[%c0] : memref<4xi32>
                        scf.yield
                    }
                    return
                }
            }
        "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let if_operation = super::util::BlockIter::new(function.first_region().unwrap().first_block().unwrap())
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.if")
        .unwrap();

    let capability_map = compute_capabilities(&module);
    let if_capabilities = &capability_map[&if_operation.to_raw().ptr];
    let function_capabilities = &capability_map[&function.to_raw().ptr];

    assert_eq!(format_capabilities(if_capabilities), "arg0: uniq @ 0..0");
    assert_eq!(format_capabilities(function_capabilities), "arg0: uniq @ 0..0");
}

#[test]
fn block_capabilities_coalesces_loop_before_lower_bound_substitution() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
            module {
                func.func @test(%array: memref<4xi32>, %value: i32) {
                    %c0 = arith.constant 0 : index
                    %c1 = arith.constant 1 : index
                    %c4 = arith.constant 4 : index
                    scf.for %i = %c0 to %c4 step %c1 {
                        %loaded = memref.load %array[%i] : memref<4xi32>
                        memref.store %value, %array[%i] : memref<4xi32>
                        scf.yield
                    }
                    return
                }
            }
        "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let for_loop = super::util::BlockIter::new(function.first_region().unwrap().first_block().unwrap())
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();

    let capability_map = compute_capabilities(&module);
    let loop_capabilities = &capability_map[&for_loop.to_raw().ptr];
    let function_capabilities = &capability_map[&function.to_raw().ptr];

    assert_eq!(format_capabilities(loop_capabilities), "arg0: uniq @ i..3");
    assert_eq!(format_capabilities(function_capabilities), "arg0: uniq @ 0..3");
}

#[test]
fn block_capabilities_promotes_loop_access_and_finds_parent_iterator() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @read(%array: memref<8xi32>) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c4 = arith.constant 4 : index
                        scf.for %i = %c0 to %c4 step %c1 {
                            %value = memref.load %array[%i] : memref<8xi32>
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut current = body.first_operation().unwrap();
    let for_loop = loop {
        if current.name().as_string_ref().as_str().unwrap() == "scf.for" {
            break current;
        }
        current = current.next_in_block().unwrap();
    };
    let loop_body = for_loop.first_region().unwrap().first_block().unwrap();
    let iterator: Value<'_, '_> = loop_body.argument(0).unwrap().into();
    let load = loop_body.first_operation().unwrap();
    let found_iterator = find_parent_iterator(load).unwrap();
    assert_eq!(found_iterator.to_raw().ptr, iterator.to_raw().ptr);

    let mut capabilities = vec![];
    let mut capability_map = HashMap::new();
    block_capabilities(body, &mut capability_map, &mut capabilities);

    assert_eq!(capabilities.len(), 1);
    assert_eq!(capabilities[0].capability_type, CapabilityType::Shrd);
    let (start, end) = capabilities[0].capability_expr.as_ref().unwrap();
    assert!(matches!(start, CapabilityExpr::Constant(0)));
    assert_eq!(end.constant_propagate(), Some(3));

    let loop_capabilities = capability_map.get(&for_loop.to_raw().ptr).unwrap();
    println!(
        "shared loop capabilities: [{}]",
        format_capabilities(loop_capabilities)
    );
    assert_eq!(loop_capabilities.len(), 1);
    assert_eq!(loop_capabilities[0].capability_type, CapabilityType::Shrd);
    let (start, end) = loop_capabilities[0].capability_expr.as_ref().unwrap();
    assert_eq!(start.to_string(), "i");
    assert_eq!(end.constant_propagate(), Some(3));
}

#[test]
fn for_loop_parameters_include_upper_bound_and_symbolic_step() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @write(%array: memref<16xi32>, %lower: index, %upper: index, %step: index, %value: i32) {
                        scf.for %i = %lower to %upper step %step {
                            memref.store %value, %array[%i] : memref<16xi32>
                            scf.yield
                        }
                        return
                    }
                    func.func @constant_step(%array: memref<16xi32>, %lower: index, %upper: index, %value: i32) {
                        %c1 = arith.constant 1 : index
                        scf.for %i = %lower to %upper step %c1 {
                            memref.store %value, %array[%i] : memref<16xi32>
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let lower: Value<'_, '_> = body.argument(1).unwrap().into();
    let upper: Value<'_, '_> = body.argument(2).unwrap().into();
    let step: Value<'_, '_> = body.argument(3).unwrap().into();
    let for_loop = super::util::BlockIter::new(body)
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();

    let (upper_parameter, step_parameter) = super::for_loop_parameter_values(for_loop);

    let super::ForLoopParameterValue::Variable(upper_parameter) = upper_parameter else {
        unreachable!()
    };
    let super::ForLoopParameterValue::Variable(step_parameter) = step_parameter else {
        unreachable!()
    };
    assert_eq!(upper_parameter.name, super::value_to_name(&upper));
    assert_eq!(step_parameter.name, super::value_to_name(&step));
    assert_ne!(upper_parameter.name, super::value_to_name(&lower));

    let constant_step_function = function.next_in_block().unwrap();
    let constant_step_body = constant_step_function
        .first_region()
        .unwrap()
        .first_block()
        .unwrap();
    let constant_step_loop = super::util::BlockIter::new(constant_step_body)
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();
    let (constant_upper, constant_step) = super::for_loop_parameter_values(constant_step_loop);
    assert!(matches!(constant_upper, super::ForLoopParameterValue::Variable(_)));
    assert!(matches!(constant_step, super::ForLoopParameterValue::Constant(1)));
}

#[test]
fn for_loop_function_parameters_include_unused_iter_args() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @carry(%lower: index, %upper: index, %initial: i32) -> i32 {
                        %c1 = arith.constant 1 : index
                        %result = scf.for %i = %lower to %upper step %c1
                            iter_args(%carried = %initial) -> i32 {
                            %next = arith.constant 7 : i32
                            scf.yield %next : i32
                        }
                        return %result : i32
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let for_loop = super::util::BlockIter::new(body)
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();
    let loop_body = for_loop.first_region().unwrap().first_block().unwrap();
    let iteration: Value<'_, '_> = loop_body.argument(0).unwrap().into();
    let carried: Value<'_, '_> = loop_body.argument(1).unwrap().into();
    let (upper_bound, step) = super::for_loop_parameter_values(for_loop);

    let (parameters, _) = super::for_loop_function_captures(for_loop, &upper_bound, &step);

    assert!(parameters
        .iter()
        .any(|parameter| parameter.name == super::value_to_name(&iteration)));
    assert!(parameters
        .iter()
        .any(|parameter| parameter.name == super::value_to_name(&carried)));
}

#[test]
fn block_to_wavelet_uses_scf_yield_as_the_loop_body_tail() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @carry(%initial: i32) -> i32 {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %result = scf.for %i = %c0 to %c1 step %c1
                            iter_args(%carried = %initial) -> i32 {
                            scf.yield %carried : i32
                        }
                        return %result : i32
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let for_loop = super::util::BlockIter::new(body)
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();
    let loop_body = for_loop.first_region().unwrap().first_block().unwrap();
    let yielded = loop_body.first_operation().unwrap().operand(0).unwrap();
    let mut program = wavelet_elab::Program::new();
    let mut capability_map = HashMap::new();

    let expression = super::block_to_wavelet(
        loop_body,
        &mut program,
        None,
        &mut capability_map,
    );

    assert_eq!(
        expression.tail,
        wavelet_elab::Tail::RetVar(wavelet_elab::UntypedVar(super::value_to_name(&yielded)))
    );
}

#[test]
fn block_to_wavelet_makes_a_directly_yielded_if_the_tail() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @carry(%condition: i1, %initial: i32) -> i32 {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %result = scf.for %i = %c0 to %c1 step %c1
                            iter_args(%carried = %initial) -> i32 {
                            %selected = scf.if %condition -> i32 {
                                %then_value = arith.constant 7 : i32
                                scf.yield %then_value : i32
                            } else {
                                %else_value = arith.constant 9 : i32
                                scf.yield %else_value : i32
                            }
                            scf.yield %selected : i32
                        }
                        return %result : i32
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let for_loop = super::util::BlockIter::new(body)
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();
    let loop_body = for_loop.first_region().unwrap().first_block().unwrap();
    let iteration: Value<'_, '_> = loop_body.argument(0).unwrap().into();
    let carried: Value<'_, '_> = loop_body.argument(1).unwrap().into();
    let iteration = wavelet_elab::UntypedVar(super::value_to_name(&iteration));
    let carried = wavelet_elab::UntypedVar(super::value_to_name(&carried));
    let next_iteration = wavelet_elab::UntypedVar("next_iteration".to_string());
    let function_name = wavelet_elab::FnName("loop".to_string());
    let information = super::TailCallInformation {
        function_name: function_name.clone(),
        parameters: vec![
            wavelet_elab::TypedVar {
                name: iteration.0.clone(),
                ty: wavelet_elab::Ty::Int(wavelet_elab::ir::Signedness::Signed),
            },
            wavelet_elab::TypedVar {
                name: carried.0.clone(),
                ty: wavelet_elab::Ty::Int(wavelet_elab::ir::Signedness::Signed),
            },
        ],
        iteration_argument: iteration,
        next_iteration: next_iteration.clone(),
        carried_argument: Some(carried),
    };
    let mut program = wavelet_elab::Program::new();
    let mut capability_map = HashMap::new();

    let expression = super::block_to_wavelet(
        loop_body,
        &mut program,
        Some(&information),
        &mut capability_map,
    );

    let wavelet_elab::Tail::IfElse { then_e, else_e, .. } = expression.tail else {
        unreachable!()
    };
    assert!(program.defs.is_empty());
    for branch in [*then_e, *else_e] {
        let yielded = match branch.stmts.last().unwrap() {
            wavelet_elab::Stmt::LetVal { var, .. } => var.clone(),
            _ => unreachable!(),
        };
        let wavelet_elab::Tail::TailCall { func, args } = branch.tail else {
            unreachable!()
        };
        assert_eq!(func, function_name);
        assert_eq!(args[0], next_iteration);
        assert_eq!(args[1], yielded);
    }
}

#[test]
fn block_to_wavelet_outlines_a_non_tail_if() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @choose(%condition: i1, %input: i32) -> i32 {
                        %selected = scf.if %condition -> i32 {
                            %then_value = arith.addi %input, %input : i32
                            scf.yield %then_value : i32
                        } else {
                            %else_value = arith.subi %input, %input : i32
                            scf.yield %else_value : i32
                        }
                        %result = arith.addi %selected, %input : i32
                        return %result : i32
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let block = function.first_region().unwrap().first_block().unwrap();
    let if_statement = block.first_operation().unwrap();
    let mut capability_map = HashMap::new();
    let mut capabilities = Vec::new();
    block_capabilities(block, &mut capability_map, &mut capabilities);
    let mut program = wavelet_elab::Program::new();

    let expression = super::block_to_wavelet(
        block,
        &mut program,
        None,
        &mut capability_map,
    );

    let wavelet_elab::Stmt::LetCall { vars, func, args, .. } = &expression.stmts[0] else {
        unreachable!()
    };
    assert_eq!(vars[0].0, super::value_to_name(&if_statement.result(0).unwrap().into()));
    assert_eq!(program.defs.len(), 1);
    let outlined = &program.defs[0];
    assert_eq!(func, &outlined.name);
    assert_eq!(args.len(), outlined.params.len());
    assert!(matches!(outlined.body.tail, wavelet_elab::Tail::IfElse { .. }));
}

#[test]
fn block_capabilities_tracks_increasing_and_decreasing_unique_loop_caps() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @write(%increasing: memref<4xi32>, %decreasing: memref<4xi32>, %value: i32) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c2 = arith.constant 2 : index
                        %c3 = arith.constant 3 : index
                        %c4 = arith.constant 4 : index
                        scf.for %i = %c2 to %c4 step %c1 {
                            memref.store %value, %increasing[%i] : memref<4xi32>
                            scf.yield
                        }
                        scf.for %i = %c0 to %c4 step %c1 {
                            %index = arith.subi %c3, %i : index
                            memref.store %value, %decreasing[%index] : memref<4xi32>
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let loops: Vec<_> = super::util::BlockIter::new(body)
        .filter(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .collect();
    let mut capability_map = HashMap::new();
    let mut capabilities = Vec::new();

    block_capabilities(body, &mut capability_map, &mut capabilities);

    let increasing = capability_map.get(&loops[0].to_raw().ptr).unwrap();
    println!(
        "increasing loop capabilities: [{}]",
        format_capabilities(increasing)
    );
    assert_eq!(increasing.len(), 1);
    assert_eq!(increasing[0].capability_type, CapabilityType::Uniq);
    let (uniq_start, uniq_end) = increasing[0].capability_expr.as_ref().unwrap();
    assert_eq!(uniq_start.to_string(), "i");
    assert_eq!(uniq_end.constant_propagate(), Some(3));

    let decreasing = capability_map.get(&loops[1].to_raw().ptr).unwrap();
    println!(
        "decreasing loop capabilities: [{}]",
        format_capabilities(decreasing)
    );
    assert_eq!(decreasing.len(), 1);
    assert_eq!(decreasing[0].capability_type, CapabilityType::Uniq);
    let (uniq_start, uniq_end) = decreasing[0].capability_expr.as_ref().unwrap();
    assert_eq!(uniq_start.constant_propagate(), Some(0));
    assert_eq!(uniq_end.to_string(), "3 - i");
}

#[test]
fn block_capabilities_keeps_poison_for_loop_caps_poisoned() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @write(%array: memref<16xi32>, %value: i32) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c4 = arith.constant 4 : index
                        scf.for %i = %c0 to %c4 step %c1 {
                            %shifted = arith.subi %i, %c1 : index
                            %index = arith.muli %shifted, %shifted : index
                            memref.store %value, %array[%index] : memref<16xi32>
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let for_loop = super::util::BlockIter::new(body)
        .find(|operation| operation.name().as_string_ref().as_str().unwrap() == "scf.for")
        .unwrap();
    let mut capability_map = HashMap::new();
    let mut capabilities = Vec::new();

    block_capabilities(body, &mut capability_map, &mut capabilities);

    let loop_capabilities = capability_map.get(&for_loop.to_raw().ptr).unwrap();
    println!(
        "poisoned loop capabilities: [{}]",
        format_capabilities(loop_capabilities)
    );
    assert_eq!(loop_capabilities.len(), 1);
    assert_eq!(loop_capabilities[0].capability_type, CapabilityType::Uniq);
    assert!(loop_capabilities[0].capability_expr.is_none());
}

#[test]
fn block_capabilities_handles_flattened_2d_array_access() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @read_2d(%array: memref<100xi32>) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c10 = arith.constant 10 : index
                        scf.for %i = %c0 to %c10 step %c1 {
                            scf.for %j = %c0 to %c10 step %c1 {
                                %width = arith.constant 10 : index
                                %row = arith.muli %i, %width : index
                                %index = arith.addi %row, %j : index
                                %value = memref.load %array[%index] : memref<100xi32>
                                scf.yield
                            }
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut capabilities = vec![];

    let mut capability_map = HashMap::new();
    block_capabilities(body, &mut capability_map, &mut capabilities);

    assert_eq!(capabilities.len(), 1);
    assert_eq!(capabilities[0].capability_type, CapabilityType::Shrd);
    let (start, end) = capabilities[0].capability_expr.as_ref().unwrap();
    assert_eq!(start.constant_propagate(), Some(0));
    assert_eq!(end.constant_propagate(), Some(99));
}

#[test]
fn block_capabilities_handles_nested_quadratic_access() {
    let context = test_context();
    let module = Module::parse(&context, include_str!("../complicated_access.mlir")).unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut capabilities = vec![];

    let mut capability_map = HashMap::new();
    block_capabilities(body, &mut capability_map, &mut capabilities);

    assert_eq!(capabilities.len(), 1);
    assert_eq!(capabilities[0].capability_type, CapabilityType::Uniq);
    assert!(capabilities[0].capability_expr.is_none());
}

#[test]
fn block_capabilities_handles_increasing_then_decreasing_accesses() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @bidirectional_access(%array: memref<11xi32>) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c10 = arith.constant 10 : index
                        %c11 = arith.constant 11 : index
                        scf.for %i = %c0 to %c11 step %c1 {
                            %increasing = memref.load %array[%i] : memref<11xi32>
                            %decreasing_index = arith.subi %c10, %i : index
                            %decreasing = memref.load %array[%decreasing_index] : memref<11xi32>
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut capabilities = vec![];

    let mut capability_map = HashMap::new();
    block_capabilities(body, &mut capability_map, &mut capabilities);

    assert_eq!(capabilities.len(), 2);
    for capability in &capabilities {
        assert_eq!(capability.capability_type, CapabilityType::Shrd);
        let (start, end) = capability.capability_expr.as_ref().unwrap();
        assert_eq!(start.constant_propagate(), Some(0));
        assert_eq!(end.constant_propagate(), Some(10));
    }
}

#[test]
fn block_capabilities_handles_increasing_intervals_with_decreasing_indices() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @increasing_intervals(%array: memref<100xi32>) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c9 = arith.constant 9 : index
                        %c10 = arith.constant 10 : index
                        scf.for %i = %c0 to %c10 step %c1 {
                            %interval_start = arith.muli %i, %c10 : index
                            scf.for %j = %c0 to %c10 step %c1 {
                                %decreasing_index = arith.subi %c9, %j : index
                                %index = arith.addi %interval_start, %decreasing_index : index
                                %value = memref.load %array[%index] : memref<100xi32>
                                scf.yield
                            }
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut capabilities = vec![];

    let mut capability_map = HashMap::new();
    block_capabilities(body, &mut capability_map, &mut capabilities);

    assert_eq!(capabilities.len(), 1);
    assert_eq!(capabilities[0].capability_type, CapabilityType::Shrd);
    let (start, end) = capabilities[0].capability_expr.as_ref().unwrap();
    assert_eq!(start.constant_propagate(), Some(0));
    assert_eq!(end.constant_propagate(), Some(99));
}

#[test]
fn block_capabilities_handles_decreasing_intervals_with_increasing_indices() {
    let context = test_context();
    let module = Module::parse(
        &context,
        r#"
                module {
                    func.func @decreasing_intervals(%array: memref<100xi32>) {
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c9 = arith.constant 9 : index
                        %c10 = arith.constant 10 : index
                        scf.for %i = %c0 to %c10 step %c1 {
                            %decreasing_interval = arith.subi %c9, %i : index
                            %interval_start = arith.muli %decreasing_interval, %c10 : index
                            scf.for %j = %c0 to %c10 step %c1 {
                                %index = arith.addi %interval_start, %j : index
                                %value = memref.load %array[%index] : memref<100xi32>
                                scf.yield
                            }
                            scf.yield
                        }
                        return
                    }
                }
            "#,
    )
    .unwrap();
    let function = module.body().first_operation().unwrap();
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut capabilities = vec![];

    let mut capability_map = HashMap::new();
    block_capabilities(body, &mut capability_map, &mut capabilities);

    assert_eq!(capabilities.len(), 1);
    assert_eq!(capabilities[0].capability_type, CapabilityType::Shrd);
    let (start, end) = capabilities[0].capability_expr.as_ref().unwrap();
    assert_eq!(start.constant_propagate(), Some(0));
    assert_eq!(end.constant_propagate(), Some(99));
}
