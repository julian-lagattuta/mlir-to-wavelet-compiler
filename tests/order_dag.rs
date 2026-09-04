mod implementation {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/fence_placement.rs"
    ));

    use wavelet_elab::ir::{ArrayLen, Signedness};

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
            _ => name(node).to_owned(),
        }
    }

    fn ordered_labels(stmts: &[Stmt<TypedVar>]) -> Vec<String> {
        order_dag(
            stmts_to_dag(stmts, &HashMap::new()),
            Bool::from_bool(true),
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

        let stmts = order_to_stmts(vec![FenceOrNode::Node(variable), FenceOrNode::Fence]);

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
