mod capabilities {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) enum CapabilityType {
        Shrd,
        Uniq,
    }
}

mod implementation {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/fence_placement.rs"
    ));

    use wavelet_elab::{
        Tail,
        ir::ArrayLen,
        logic::{cap::CapPattern, region::Region},
    };

    fn int(name: &str) -> TypedVar {
        TypedVar::new(name, Ty::Int(Signedness::Signed))
    }

    fn array(name: &str) -> TypedVar {
        TypedVar::new(
            name,
            Ty::RefUniq {
                elem: Box::new(Ty::Int(Signedness::Signed)),
                len: ArrayLen::Const(16),
            },
        )
    }

    fn let_int(var: &TypedVar, value: i64) -> Stmt<TypedVar> {
        Stmt::LetVal {
            var: var.clone(),
            val: Val::Int(value),
            fence: false,
        }
    }

    fn store(array: &TypedVar, index: &TypedVar, value: &TypedVar) -> Stmt<TypedVar> {
        Stmt::LetOp {
            vars: Vec::new(),
            op: Op::Store {
                array: array.clone(),
                index: index.clone(),
                value: value.clone(),
                len: ArrayLen::Const(16),
            },
            fence: false,
        }
    }

    fn load(result: &TypedVar, array: &TypedVar, index: &TypedVar) -> Stmt<TypedVar> {
        Stmt::LetOp {
            vars: vec![result.clone()],
            op: Op::Load {
                array: array.clone(),
                index: index.clone(),
                len: ArrayLen::Const(16),
            },
            fence: false,
        }
    }

    fn unique_callee(name: &str) -> FnDef<TypedVar> {
        let index = int("formal_index");
        let destination = array("formal_array");
        FnDef {
            name: FnName(name.to_owned()),
            params: vec![index.clone(), destination.clone()],
            alloc_arrays: Vec::new(),
            caps: vec![CapPattern {
                array: destination.name,
                len: ArrayLen::Const(16),
                uniq: Some(Region::from_bounded(
                    Idx::Var(index.name.clone()),
                    Idx::Add(
                        Box::new(Idx::Var(index.name)),
                        Box::new(Idx::Const(1)),
                    ),
                )),
                shrd: None,
            }],
            returns: Ty::Unit,
            body: Expr {
                stmts: Vec::new(),
                tail: Tail::RetVar(TypedVar::new("unused", Ty::Unit)),
            },
        }
    }

    fn name(node: &Rc<Node>) -> &str {
        &node.var.as_ref().expect("named test node").name
    }

    fn label(node: &Rc<Node>) -> String {
        match &node.op {
            NodeOp::Write { array, idx, .. } => {
                format!("write:{}[{}]", name(array), name(idx))
            }
            NodeOp::Read { array, idx } => {
                format!("read:{}={}[{}]", name(node), name(array), name(idx))
            }
            NodeOp::Initial(_) => "initial".to_owned(),
            NodeOp::TailCall(function, _) => format!("tail:{}", function.0),
            _ => name(node).to_owned(),
        }
    }

    fn ordered_labels(stmts: &[Stmt<TypedVar>]) -> Vec<String> {
        order_dag(
            stmts_to_dag(stmts, &HashMap::new(), HashMap::new(), None),
            &Bool::from_bool(true),
            &HashMap::new(),
        )
            .into_iter()
            .map(|item| match item {
                FenceOrNode::Fence => "fence".to_owned(),
                FenceOrNode::Node(node) => label(&node),
            })
            .collect()
    }

    fn ordered_labels_with_tail(
        stmts: &[Stmt<TypedVar>],
        tail_function: &FnName,
        tail_args: &[TypedVar],
        functions: &HashMap<String, FnDef<TypedVar>>,
    ) -> Vec<String> {
        order_dag(
            stmts_to_dag(
                stmts,
                functions,
                HashMap::new(),
                Some((tail_function, tail_args)),
            ),
            &Bool::from_bool(true),
            functions,
        )
        .into_iter()
        .map(|item| match item {
            FenceOrNode::Fence => "fence".to_owned(),
            FenceOrNode::Node(node) => label(&node),
        })
        .collect()
    }

    fn position(order: &[String], label: &str) -> usize {
        let positions: Vec<_> = order
            .iter()
            .enumerate()
            .filter_map(|(position, item)| (item == label).then_some(position))
            .collect();
        assert_eq!(
            positions.len(),
            1,
            "expected exactly one {label:?} in {order:?}"
        );
        positions[0]
    }

    fn assert_before(order: &[String], dependency: &str, user: &str) {
        assert!(
            position(order, dependency) < position(order, user),
            "expected {dependency:?} before {user:?}, got {order:?}"
        );
    }

    fn conflicting_accesses_are_ordered_across_a_fence() {
        let a = array("a");
        let i = int("i");
        let j = int("j");
        let value = int("value");
        let loaded = int("loaded");
        let stmts = vec![
            let_int(&i, 0),
            let_int(&j, 0),
            let_int(&value, 7),
            store(&a, &i, &value),
            load(&loaded, &a, &j),
        ];

        let order = ordered_labels(&stmts);
        let write = position(&order, "write:a[i]");
        let read = position(&order, "read:loaded=a[j]");

        assert_before(&order, "a", "write:a[i]");
        assert_before(&order, "i", "write:a[i]");
        assert_before(&order, "value", "write:a[i]");
        assert_before(&order, "a", "read:loaded=a[j]");
        assert_before(&order, "j", "read:loaded=a[j]");
        assert!(
            write < read,
            "the earlier conflicting access moved after the later one: {order:?}"
        );
        assert!(
            order[write + 1..read].iter().any(|item| item == "fence"),
            "conflicting accesses were not separated by a fence: {order:?}"
        );
    }

    fn conflicting_accesses_can_use_the_same_index_node() {
        let a = array("a");
        let i = int("i");
        let value = int("value");
        let loaded = int("loaded");
        let stmts = vec![
            let_int(&i, 0),
            let_int(&value, 7),
            store(&a, &i, &value),
            load(&loaded, &a, &i),
        ];

        let order = ordered_labels(&stmts);
        let write = position(&order, "write:a[i]");
        let read = position(&order, "read:loaded=a[i]");

        assert!(
            write < read,
            "conflicting accesses were reordered: {order:?}"
        );
        assert!(
            order[write + 1..read].iter().any(|item| item == "fence"),
            "conflicting accesses using the same index were not fenced: {order:?}"
        );
    }

    fn two_reads_of_the_same_location_do_not_conflict() {
        let a = array("a");
        let i = int("i");
        let first_result = int("first_result");
        let second_result = int("second_result");
        let stmts = vec![
            let_int(&i, 0),
            load(&first_result, &a, &i),
            load(&second_result, &a, &i),
        ];

        let order = ordered_labels(&stmts);
        let first = position(&order, "read:first_result=a[i]");
        let second = position(&order, "read:second_result=a[i]");
        let (first, second) = (first.min(second), first.max(second));

        assert!(
            order[first + 1..second].iter().all(|item| item != "fence"),
            "two reads of the same location were separated: {order:?}"
        );
    }

    fn combined_data_and_memory_dependency_is_emitted_once() {
        let a = array("a");
        let i = int("i");
        let j = int("j");
        let loaded = int("loaded");
        let stmts = vec![
            let_int(&i, 0),
            let_int(&j, 0),
            load(&loaded, &a, &i),
            store(&a, &j, &loaded),
        ];

        let order = ordered_labels(&stmts);
        let read = position(&order, "read:loaded=a[i]");
        let write = position(&order, "write:a[j]");

        assert!(read < write, "the data dependency was reversed: {order:?}");
        assert!(
            order[read + 1..write].iter().any(|item| item == "fence"),
            "the memory dependency did not cross a fence: {order:?}"
        );
    }

    fn provably_disjoint_accesses_stay_in_the_same_fence_group() {
        let a = array("a");
        let i = int("i");
        let j = int("j");
        let value = int("value");
        let loaded = int("loaded");
        let stmts = vec![
            let_int(&i, 0),
            let_int(&j, 1),
            let_int(&value, 7),
            store(&a, &i, &value),
            load(&loaded, &a, &j),
        ];

        let order = ordered_labels(&stmts);
        let first = position(&order, "write:a[i]").min(position(&order, "read:loaded=a[j]"));
        let second = position(&order, "write:a[i]").max(position(&order, "read:loaded=a[j]"));

        assert!(
            order[first + 1..second].iter().all(|item| item != "fence"),
            "disjoint accesses were unnecessarily separated: {order:?}"
        );
    }

    fn accesses_to_different_arrays_stay_in_the_same_fence_group() {
        let a = array("a");
        let b = array("b");
        let i = int("i");
        let j = int("j");
        let value = int("value");
        let loaded = int("loaded");
        let stmts = vec![
            let_int(&i, 0),
            let_int(&j, 0),
            let_int(&value, 7),
            store(&a, &i, &value),
            load(&loaded, &b, &j),
        ];

        let order = ordered_labels(&stmts);
        let first = position(&order, "write:a[i]").min(position(&order, "read:loaded=b[j]"));
        let second = position(&order, "write:a[i]").max(position(&order, "read:loaded=b[j]"));

        assert!(
            order[first + 1..second].iter().all(|item| item != "fence"),
            "accesses to different arrays were unnecessarily separated: {order:?}"
        );
    }

    fn operation_results_follow_their_dependencies() {
        let a = array("a");
        let i = int("i");
        let one = int("one");
        let loaded = int("loaded");
        let sum = int("sum");
        let stmts = vec![
            let_int(&i, 0),
            let_int(&one, 1),
            load(&loaded, &a, &i),
            Stmt::LetOp {
                vars: vec![loaded.clone(), one.clone(), sum.clone()],
                op: Op::Add,
                fence: false,
            },
        ];

        let order = ordered_labels(&stmts);
        assert_before(&order, "a", "read:loaded=a[i]");
        assert_before(&order, "i", "read:loaded=a[i]");
        assert_before(&order, "read:loaded=a[i]", "sum");
        assert_before(&order, "one", "sum");
    }

    fn conflicting_tail_call_is_terminal_and_fenced() {
        let output = array("output");
        let store_index = int("store_index");
        let call_index = int("call_index");
        let value = int("value");
        let function = unique_callee("fill");
        let function_name = function.name.clone();
        let functions = HashMap::from([(function_name.0.clone(), function)]);
        let stmts = vec![
            let_int(&store_index, 0),
            let_int(&call_index, 0),
            let_int(&value, 7),
            store(&output, &store_index, &value),
        ];
        let tail_args = vec![call_index, output];

        let order = ordered_labels_with_tail(
            &stmts,
            &function_name,
            &tail_args,
            &functions,
        );
        let store = position(&order, "write:output[store_index]");
        let tail = position(&order, "tail:fill");

        assert_eq!(tail, order.len() - 1, "tail call was not terminal: {order:?}");
        assert!(
            order[store + 1..tail].iter().any(|item| item == "fence"),
            "conflicting tail call was not fenced: {order:?}"
        );

        let mut expr = Expr {
            stmts,
            tail: Tail::TailCall {
                func: function_name,
                args: tail_args,
            },
        };
        place_fences_expr(
            &mut expr,
            &Bool::from_bool(true),
            HashMap::new(),
            &functions,
        );

        assert!(matches!(expr.tail, Tail::TailCall { .. }));
        assert!(matches!(
            expr.stmts.last(),
            Some(Stmt::LetOp { fence: true, .. })
        ));
    }

    fn scalar_call_arguments_are_substituted_in_capabilities() {
        let output = array("output");
        let store_index = int("store_index");
        let call_index = int("call_index");
        let value = int("value");
        let function = unique_callee("fill");
        let function_name = function.name.clone();
        let functions = HashMap::from([(function_name.0.clone(), function)]);
        let stmts = vec![
            let_int(&store_index, 0),
            let_int(&call_index, 1),
            let_int(&value, 7),
            store(&output, &store_index, &value),
        ];
        let tail_args = vec![call_index, output];

        let order = ordered_labels_with_tail(
            &stmts,
            &function_name,
            &tail_args,
            &functions,
        );
        let store = position(&order, "write:output[store_index]");
        let tail = position(&order, "tail:fill");

        assert_eq!(tail, order.len() - 1, "tail call was not terminal: {order:?}");
        assert!(
            order[store + 1..tail].iter().all(|item| item != "fence"),
            "disjoint substituted tail-call capability was fenced: {order:?}"
        );
    }

    fn unfenced_parent_accesses_are_propagated_into_branches() {
        let output = array("output");
        let index = int("index");
        let value = int("value");
        let condition = TypedVar::new("condition", Ty::Bool);
        let loaded = int("loaded");
        let mut expr = Expr {
            stmts: vec![
                let_int(&index, 0),
                let_int(&value, 7),
                Stmt::LetVal {
                    var: condition.clone(),
                    val: Val::Bool(true),
                    fence: false,
                },
                store(&output, &index, &value),
            ],
            tail: Tail::IfElse {
                cond: condition,
                then_e: Box::new(Expr {
                    stmts: vec![load(&loaded, &output, &index)],
                    tail: Tail::RetVar(loaded),
                }),
                else_e: Box::new(Expr {
                    stmts: Vec::new(),
                    tail: Tail::RetVar(value),
                }),
            },
        };

        place_fences_expr(
            &mut expr,
            &Bool::from_bool(true),
            HashMap::new(),
            &HashMap::new(),
        );

        let Tail::IfElse { then_e, .. } = expr.tail else {
            panic!("expected if tail")
        };
        assert!(matches!(
            then_e.stmts.first(),
            Some(Stmt::LetVal {
                val: Val::Unit,
                fence: true,
                ..
            })
        ));
        assert!(matches!(
            then_e.stmts.get(1),
            Some(Stmt::LetOp { op: Op::Load { .. }, .. })
        ));
    }

    fn empty_body_can_emit_a_fence_before_its_tail_call() {
        let output = array("output");
        let index = int("index");
        let function = unique_callee("fill");
        let function_name = function.name.clone();
        let functions = HashMap::from([(function_name.0.clone(), function)]);
        let point = Int::new_const("cool").eq(Int::new_const(index.name.clone()));
        let initial_capabilities = HashMap::from([(
            output.name.clone(),
            (Bool::from_bool(false), point),
        )]);
        let mut expr = Expr {
            stmts: Vec::new(),
            tail: Tail::TailCall {
                func: function_name,
                args: vec![index, output],
            },
        };

        place_fences_expr(
            &mut expr,
            &Bool::from_bool(true),
            initial_capabilities,
            &functions,
        );

        assert!(matches!(expr.tail, Tail::TailCall { .. }));
        assert_eq!(expr.stmts.len(), 1);
        assert!(matches!(
            &expr.stmts[0],
            Stmt::LetVal {
                val: Val::Unit,
                fence: true,
                ..
            }
        ));
    }

    #[test]
    fn child_order_dag_case() {
        let Ok(case) = std::env::var("ORDER_DAG_TEST_CASE") else {
            return;
        };

        match case.as_str() {
            "conflicting" => conflicting_accesses_are_ordered_across_a_fence(),
            "same_index" => conflicting_accesses_can_use_the_same_index_node(),
            "read_read" => two_reads_of_the_same_location_do_not_conflict(),
            "data_and_memory" => combined_data_and_memory_dependency_is_emitted_once(),
            "disjoint" => provably_disjoint_accesses_stay_in_the_same_fence_group(),
            "different_arrays" => accesses_to_different_arrays_stay_in_the_same_fence_group(),
            "topological" => operation_results_follow_their_dependencies(),
            "tail_conflict" => conflicting_tail_call_is_terminal_and_fenced(),
            "tail_substitution" => scalar_call_arguments_are_substituted_in_capabilities(),
            "branch_initial" => unfenced_parent_accesses_are_propagated_into_branches(),
            "empty_tail_fence" => empty_body_can_emit_a_fence_before_its_tail_call(),
            _ => panic!("unknown order_dag test case {case:?}"),
        }
    }

    #[test]
    fn variable_at_a_fence_boundary_emits_a_fenced_unit_binding() {
        let variable = Rc::new(Node {
            op: NodeOp::Variable,
            var: Some(int("free")),
            parents: Default::default(),
            fence_parents: Default::default(),
        });

        let order = vec![FenceOrNode::Node(variable), FenceOrNode::Fence];
        let stmts = order_to_stmts(&order);

        assert_eq!(stmts.len(), 1);
        let Stmt::LetVal {
            var,
            val: Val::Unit,
            fence: true,
        } = &stmts[0]
        else {
            panic!("expected a fenced dummy unit binding, got {:?}", stmts[0]);
        };
        assert_eq!(var.ty, Ty::Unit);
        assert!(var.name.starts_with("_fence_dummy_"));
    }

    #[test]
    fn initial_at_a_fence_boundary_emits_a_fenced_unit_binding() {
        let initial = Rc::new(Node {
            op: NodeOp::Initial(HashMap::new()),
            var: None,
            parents: Default::default(),
            fence_parents: Default::default(),
        });
        let order = vec![FenceOrNode::Node(initial), FenceOrNode::Fence];

        let stmts = order_to_stmts(&order);

        assert_eq!(stmts.len(), 1);
        assert!(matches!(
            &stmts[0],
            Stmt::LetVal {
                val: Val::Unit,
                fence: true,
                ..
            }
        ));
    }

    #[test]
    fn unfenced_initial_capabilities_are_propagated() {
        let index = Int::new_const("cool");
        let initial_uniq = index.eq(Int::from_i64(3));
        let initial = Rc::new(Node {
            op: NodeOp::Initial(HashMap::from([(
                "output".to_owned(),
                (Bool::from_bool(false), initial_uniq.clone()),
            )])),
            var: None,
            parents: Default::default(),
            fence_parents: Default::default(),
        });
        let order = vec![FenceOrNode::Node(initial)];

        let propagated = calculate_initial_capabilities(&order, &HashMap::new());

        let solver = Solver::new();
        assert_eq!(
            solver.check_assumptions(&[propagated["output"].1.eq(initial_uniq).not()]),
            SatResult::Unsat,
        );
    }
}

use std::{
    process::{Command, Stdio},
    thread,
    time::{Duration, Instant},
};

const CHILD_TEST: &str = "implementation::child_order_dag_case";

fn run_case(case: &str) {
    let executable = std::env::current_exe().expect("locate integration-test executable");
    let mut child = Command::new(executable)
        .args(["--exact", CHILD_TEST, "--nocapture"])
        .env("ORDER_DAG_TEST_CASE", case)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start isolated order_dag test");
    let deadline = Instant::now() + Duration::from_millis(250);

    loop {
        if child
            .try_wait()
            .expect("poll isolated order_dag test")
            .is_some()
        {
            let output = child.wait_with_output().expect("collect test output");
            assert!(
                output.status.success(),
                "order_dag case {case:?} failed\nstdout:\n{}\nstderr:\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
            );
            return;
        }

        if Instant::now() >= deadline {
            child.kill().expect("stop non-terminating order_dag test");
            child.wait().expect("reap non-terminating order_dag test");
            panic!("order_dag case {case:?} did not terminate within 250 ms");
        }

        thread::sleep(Duration::from_millis(5));
    }
}

#[test]
fn orders_conflicting_array_accesses_across_a_fence() {
    run_case("conflicting");
}

#[test]
fn orders_conflicting_accesses_that_reuse_one_index_variable() {
    run_case("same_index");
}

#[test]
fn does_not_add_a_dependency_between_two_reads() {
    run_case("read_read");
}

#[test]
fn handles_combined_data_and_memory_dependencies() {
    run_case("data_and_memory");
}

#[test]
fn does_not_add_a_dependency_between_disjoint_array_accesses() {
    run_case("disjoint");
}

#[test]
fn does_not_add_a_dependency_between_different_arrays() {
    run_case("different_arrays");
}

#[test]
fn emits_operations_in_topological_order() {
    run_case("topological");
}

#[test]
fn places_a_conflicting_tail_call_after_a_fence() {
    run_case("tail_conflict");
}

#[test]
fn substitutes_scalar_arguments_in_tail_call_capabilities() {
    run_case("tail_substitution");
}

#[test]
fn propagates_unfenced_accesses_into_branches() {
    run_case("branch_initial");
}

#[test]
fn emits_a_dummy_fence_before_an_empty_body_tail_call() {
    run_case("empty_tail_fence");
}
