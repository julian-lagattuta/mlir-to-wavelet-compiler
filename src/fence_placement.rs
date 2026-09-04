use std::{
    cell::RefCell, collections::{HashMap, HashSet, VecDeque}, debug_assert, rc::{Rc, Weak},
};

use wavelet_elab::{Expr, FnDef, FnName, Op, Program, Stmt, Ty, TypedVar, Val, ir::Signedness};
use z3::ast::{Bool, Int};
use z3::Solver;
struct Node {
    op: NodeOp,
    var: Option<TypedVar>,
    parents: RefCell<Vec<Weak<Node>>>,
    fence_parents: RefCell<Vec<Weak<Node>>>
}
enum NodeOp {
    Constant(Val),
    Call(FnName, Vec<Rc<Node>>),
    BinOp(Op<TypedVar>, Rc<Node>, Rc<Node>),
    Write {
        array: Rc<Node>,
        idx: Rc<Node>,
        value: Rc<Node>,
    },
    Read {
        array: Rc<Node>,
        idx: Rc<Node>,
    },
    Variable,
}
impl Node {
    fn z3_uniq_capabilities(&self, variable: Int)->Option<Bool>{
        match &self.op{
            NodeOp::Call(fn_name, nodes) => todo!(),
            NodeOp::Write { array, idx, value } => {
                
            },
            _ => None
        }
    }
    fn to_z3(&self) -> Option<Bool> {
        let var = self.var.as_ref()?;
        match &var.ty {
            Ty::Int(_) => self.to_z3_int_definition(),
            Ty::Bool => self.to_z3_bool_definition(),
            Ty::Unit | Ty::RefShrd { .. } | Ty::RefUniq { .. } => None,
        }
    }
    fn to_stmt(&self, fence: bool) -> Option<Stmt<TypedVar>> {
        match &self.op {
            NodeOp::Constant(val) => Some(Stmt::LetVal {
                var: self.var.clone()?,
                val: val.clone(),
                fence,
            }),
            NodeOp::Call(fn_name, nodes) => Some(Stmt::LetCall {
                vars: self.var.clone().into_iter().collect(),
                func: fn_name.clone(),
                args: nodes
                    .iter()
                    .map(|node| node.var.clone())
                    .collect::<Option<Vec<_>>>()?,
                fence,
            }),
            NodeOp::BinOp(op, lhs, rhs) => Some(Stmt::LetOp {
                vars: vec![lhs.var.clone()?, rhs.var.clone()?, self.var.clone()?],
                op: op.clone(),
                fence,
            }),
            NodeOp::Write { array, idx, value } => {
                let array = array.var.clone()?;
                let len = match &array.ty {
                    Ty::RefShrd { len, .. } | Ty::RefUniq { len, .. } => len.clone(),
                    _ => return None,
                };
                Some(Stmt::LetOp {
                    vars: Vec::new(),
                    op: Op::Store {
                        array,
                        index: idx.var.clone()?,
                        value: value.var.clone()?,
                        len,
                    },
                    fence,
                })
            }
            NodeOp::Read { array, idx } => {
                let array = array.var.clone()?;
                let len = match &array.ty {
                    Ty::RefShrd { len, .. } | Ty::RefUniq { len, .. } => len.clone(),
                    _ => return None,
                };
                Some(Stmt::LetOp {
                    vars: vec![self.var.clone()?],
                    op: Op::Load {
                        array,
                        index: idx.var.clone()?,
                        len,
                    },
                    fence,
                })
            }
            NodeOp::Variable if fence => Some(Stmt::LetVal {
                var: TypedVar::new(
                    format!("_fence_dummy_{:x}", self as *const Node as usize),
                    Ty::Unit,
                ),
                val: Val::Unit,
                fence: true,
            }),
            NodeOp::Variable => None,
        }
    }
    fn to_z3_bool(&self) -> Option<Bool> {
        let var = self.var.as_ref()?;
        matches!(var.ty, Ty::Bool).then(|| Bool::new_const(var.name.clone()))
    }

    fn to_z3_int(&self) -> Option<Int> {
        let var = self.var.as_ref()?;
        matches!(var.ty, Ty::Int(_)).then(|| Int::new_const(var.name.clone()))
    }

    fn to_z3_bool_definition(&self) -> Option<Bool> {
        let result = self.to_z3_bool()?;
        match &self.op {
            NodeOp::Constant(Val::Bool(value)) => Some(result.eq(Bool::from_bool(*value))),
            NodeOp::BinOp(op, lhs, rhs) => {
                let value = match op {
                    Op::And => Some(Bool::and(&[&lhs.to_z3_bool()?, &rhs.to_z3_bool()?])),
                    Op::Or => Some(Bool::or(&[&lhs.to_z3_bool()?, &rhs.to_z3_bool()?])),
                    Op::SignedLessThan | Op::UnsignedLessThan => {
                        Some(lhs.to_z3_int()?.lt(rhs.to_z3_int()?))
                    }
                    Op::SignedLessEqual | Op::UnsignedLessEqual => {
                        Some(lhs.to_z3_int()?.le(rhs.to_z3_int()?))
                    }
                    Op::Equal | Op::NotEqual => {
                        let equal = match &lhs.var.as_ref()?.ty {
                            Ty::Bool => lhs.to_z3_bool()?.eq(rhs.to_z3_bool()?),
                            Ty::Int(_) => lhs.to_z3_int()?.eq(rhs.to_z3_int()?),
                            _ => return None,
                        };
                        Some(if matches!(op, Op::NotEqual) {
                            equal.not()
                        } else {
                            equal
                        })
                    }
                    _ => None,
                }?;
                Some(result.eq(value))
            }
            NodeOp::Constant(_)
            | NodeOp::Call(..)
            | NodeOp::Write { .. }
            | NodeOp::Read { .. }
            | NodeOp::Variable => None,
        }
    }

    fn to_z3_int_definition(&self) -> Option<Bool> {
        let result = self.to_z3_int()?;
        match &self.op {
            NodeOp::Constant(Val::Int(value)) => Some(result.eq(Int::from_i64(*value))),
            NodeOp::BinOp(op, lhs, rhs) => {
                let lhs_value = lhs.to_z3_int()?;
                let rhs_value = rhs.to_z3_int()?;
                let value = match op {
                    Op::Add => Some(Int::add(&[&lhs_value, &rhs_value])),
                    Op::Sub => Some(Int::sub(&[&lhs_value, &rhs_value])),
                    Op::Mul => Some(Int::mul(&[&lhs_value, &rhs_value])),
                    Op::Sdiv | Op::Udiv => Some(lhs_value.div(rhs_value)),
                    _ => None,
                }?;
                Some(result.eq(value))
            }
            NodeOp::Constant(_)
            | NodeOp::Call(..)
            | NodeOp::Write { .. }
            | NodeOp::Read { .. }
            | NodeOp::Variable => None,
        }
    }
}
fn collect_free_variables(stmts: &[Stmt<TypedVar>]) -> Vec<Rc<Node>> {
    let mut bound_variables = HashSet::new();
    for stmt in stmts {
        match stmt {
            Stmt::LetVal { var, .. } => {
                bound_variables.insert(var.name.clone());
            }
            Stmt::LetOp { vars, .. } | Stmt::LetCall { vars, .. } => {
                if let Some(var) = vars.last() {
                    bound_variables.insert(var.name.clone());
                }
            }
        }
    }

    let mut seen = HashSet::new();
    let mut free_variables = Vec::new();
    let mut collect = |var: &TypedVar| {
        if !bound_variables.contains(&var.name) && seen.insert(var.name.clone()) {
            free_variables.push(Rc::new(Node {
                op: NodeOp::Variable,
                var: Some(var.clone()),
                parents: Default::default(),
                fence_parents: Default::default()
            }));
        }
    };

    for stmt in stmts {
        match stmt {
            Stmt::LetVal { .. } => {}
            Stmt::LetOp { vars, op, .. } => match op {
                Op::Load { array, index, .. } => {
                    collect(array);
                    collect(index);
                }
                Op::Store {
                    array,
                    index,
                    value,
                    ..
                } => {
                    collect(array);
                    collect(index);
                    collect(value);
                }
                _ => {
                    for var in vars.iter().take(vars.len().saturating_sub(1)) {
                        collect(var);
                    }
                }
            },
            Stmt::LetCall { args, .. } => {
                for arg in args {
                    collect(arg);
                }
            }
        }
    }

    free_variables
}
struct Dag {
    nodes: Vec<Rc<Node>>
}
fn stmts_to_dag(stmts: &[Stmt<TypedVar>]) -> Dag {
    let base_nodes = collect_free_variables(stmts);
    let mut variable_map: HashMap<String, Rc<Node>> = base_nodes
        .iter()
        .filter_map(|node| {
            node.var
                .as_ref()
                .map(|var| (var.name.clone(), node.clone()))
        })
        .collect();
    let mut nodes = base_nodes.clone();
    for stmt in stmts {
        let node = match stmt {
            Stmt::LetVal {
                var,
                val,
                fence: _,
            } => {
                let op = NodeOp::Constant(val.clone());
                Rc::new(Node {
                    op,
                    var: Some(var.clone()),
                    parents: Default::default(),
                    fence_parents: Default::default()
                })
            }
            Stmt::LetOp { vars, op, fence: _ } => {
                let op = match op {
                    Op::Load {
                        array,
                        index,
                        len: _,
                    } => {
                        let idx = variable_map.get(&index.name).unwrap();
                        let array = variable_map.get(&array.name).unwrap();

                        NodeOp::Read {
                            array: array.clone(),
                            idx: idx.clone(),
                        }
                    }
                    Op::Store {
                        array,
                        index,
                        value,
                        len: _,
                    } => {
                        let array = variable_map.get(&array.name).unwrap();
                        let idx = variable_map.get(&index.name).unwrap();
                        let value = variable_map.get(&value.name).unwrap();
                        NodeOp::Write {
                            array: array.clone(),
                            idx: idx.clone(),
                            value: value.clone(),
                        }
                    }
                    op => {
                        let a = vars.get(0).unwrap();
                        let b = vars.get(1).unwrap();
                        let a = variable_map.get(&a.name).unwrap();
                        let b = variable_map.get(&b.name).unwrap();
                        NodeOp::BinOp(op.clone(), a.clone(), b.clone())
                    }
                };
                let node = Rc::new(Node {
                    op,
                    var: vars.last().cloned(),
                    parents: Default::default(),
                    fence_parents: Default::default()
                });
                node
            }
            Stmt::LetCall {
                vars,
                func,
                args,
                fence: _,
            } => {
                let args = args
                    .iter()
                    .map(|arg| variable_map.get(&arg.name).unwrap().clone())
                    .collect();
                let node = Rc::new(Node {
                    op: NodeOp::Call(func.clone(), args),
                    var: vars.last().cloned(),
                    parents: Default::default(),
                    fence_parents: Default::default()
                });
                node
            }
        };
        let used_nodes = match &node.op {
            NodeOp::Constant(_) | NodeOp::Variable => Vec::new(),
            NodeOp::Call(_, args) => args.clone(),
            NodeOp::BinOp(_, a, b) => vec![a.clone(), b.clone()],
            NodeOp::Write { array, idx, value } => {
                vec![array.clone(), idx.clone(), value.clone()]
            }
            NodeOp::Read { array, idx } => vec![array.clone(), idx.clone()],
        };
        for used_node in used_nodes {
            used_node.parents.borrow_mut().push(Rc::downgrade(&node));
        }
        if let Some(var) = &node.var {
            variable_map.insert(var.name.clone(), node.clone());
        }
        nodes.push(node);
    }
    Dag {
        nodes,
    }
}
fn is_conflicting(idx1: &Int, idx2: &Int, solver: &Solver) -> bool {
    solver.check_assumptions(&[idx1.eq(idx2)]) != z3::SatResult::Unsat
}

enum FenceOrNode{
    Fence,
    Node(Rc<Node>)
}
fn order_dag(dag: Dag, assumptions: &Bool) -> Vec<FenceOrNode> {
    let Dag {
        nodes,
    } = dag;

    let solver = Solver::new();
    solver.assert(assumptions);
    let code_as_z3: Vec<Bool> = nodes.iter().map(|f| f.to_z3()).filter_map(|f| f).collect();
    solver.assert(Bool::and(&code_as_z3));
    for access_order in read_write_order.values() {
        for i in 0..access_order.len() {
            for j in i + 1..access_order.len() {
                let (idx1, access1) = &access_order[i];
                let (idx2, access2) = &access_order[j];
                if matches!(&access1.op, NodeOp::Read { .. })
                    && matches!(&access2.op, NodeOp::Read { .. })
                {
                    continue;
                }
                let idx1_z3 = idx1.to_z3_int().unwrap();
                let idx2_z3 = idx2.to_z3_int().unwrap();

                if is_conflicting(&idx1_z3, &idx2_z3, &solver) {
                    println!("conflict found between {} and {}", idx1_z3, idx2_z3);
                    access1
                        .fence_parents
                        .borrow_mut()
                        .push(Rc::downgrade(access2));
                }else{
                    println!("conflict not found between {} and {}", idx1_z3, idx2_z3);
                }
            }
        }
    }

    let mut dependency_counts: HashMap<*const Node, usize> = nodes
        .iter()
        .map(|node| (Rc::as_ptr(node), 0))
        .collect();
    for node in &nodes {
        for dependent in node.parents.borrow().iter() {
            let dependent = dependent.upgrade().unwrap();
            *dependency_counts.get_mut(&Rc::as_ptr(&dependent)).unwrap() += 1;
        }
        for dependent in node.fence_parents.borrow().iter() {
            let dependent = dependent.upgrade().unwrap();
            *dependency_counts.get_mut(&Rc::as_ptr(&dependent)).unwrap() += 1;
        }
    }

    let mut order = Vec::new();
    let mut fence_queue = VecDeque::new();
    let mut normal_queue: VecDeque<_> = nodes
        .iter()
        .filter(|node| dependency_counts[&Rc::as_ptr(node)] == 0)
        .cloned()
        .collect();
    let mut visited = HashSet::new();
    let mut earliest_phase: HashMap<*const Node, usize> = HashMap::new();
    let mut phase = 0;

    while !normal_queue.is_empty() {
        while let Some(node) = normal_queue.pop_front() {
            if !visited.insert(Rc::as_ptr(&node)) {
                continue;
            }
            order.push(FenceOrNode::Node(node.clone()));

            let mut release = |dependent: Rc<Node>, required_phase: usize| {
                let dependent_id = Rc::as_ptr(&dependent);
                earliest_phase
                    .entry(dependent_id)
                    .and_modify(|earliest| *earliest = (*earliest).max(required_phase))
                    .or_insert(required_phase);

                let remaining = dependency_counts.get_mut(&dependent_id).unwrap();
                *remaining = remaining.checked_sub(1).unwrap();
                if *remaining == 0 {
                    if earliest_phase[&dependent_id] > phase {
                        fence_queue.push_back(dependent);
                    } else {
                        normal_queue.push_back(dependent);
                    }
                }
            };

            for dependent in node.parents.borrow().iter() {
                release(dependent.upgrade().unwrap(), phase);
            }
            for dependent in node.fence_parents.borrow().iter() {
                release(dependent.upgrade().unwrap(), phase + 1);
            }
        }

        if !fence_queue.is_empty() {
            order.push(FenceOrNode::Fence);
            normal_queue.append(&mut fence_queue);
            phase += 1;
        }
    }

    debug_assert!({
        let v:Vec<_> = order.iter().filter(|f|matches!(f, FenceOrNode::Node(_))).collect();
        v.len() == nodes.len()
    });
    order
}
fn order_to_stmts(order: Vec<FenceOrNode>) -> Vec<Stmt<TypedVar>>{
    let mut stmts = Vec::new();
    for i in 0..order.len(){
        if let FenceOrNode::Node(node) = &order[i]{
            let fence = i + 1 < order.len() && matches!(&order[i+1], FenceOrNode::Fence);
            if let Some(x) = node.to_stmt(fence){
                stmts.push(x);
            }
        }
    }
    stmts
}
fn place_fences_expr(expr: &mut Expr<TypedVar>, assumptions: &Bool){
    let dag = stmts_to_dag(&expr.stmts);
    let order = order_dag(dag, assumptions);
    expr.stmts = order_to_stmts(order);
    match &mut expr.tail{
        wavelet_elab::Tail::IfElse { cond, then_e, else_e } => {
            let true_assumptions = Bool::and(&[assumptions, &Bool::new_const(cond.name.clone())]);
            place_fences_expr(then_e, &true_assumptions);
            let false_assumptions = Bool::and(&[assumptions, &Bool::new_const(cond.name.clone()).not()]);
            place_fences_expr(else_e, &false_assumptions);
        },
        _ => {}
    }
}
fn place_fences_fn(func: &mut FnDef<TypedVar>){
    let mut assumptions = Vec::new();
    for x in &func.params{
        if let Ty::Int(Signedness::Unsigned) = &x.ty{
            assumptions.push(Int::new_const(x.name.clone()).ge(Int::from_i64(0)));
        }
    }
    let assumptions = Bool::and(&assumptions);
    place_fences_expr(&mut func.body, &assumptions);
}
pub fn place_fences(program: &mut Program<TypedVar>){
    for func in &mut program.defs{
        place_fences_fn(func);
    }
}