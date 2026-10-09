use std::{
    cell::RefCell, collections::{HashMap, HashSet, VecDeque}, debug_assert, rc::{Rc, Weak},
};

use wavelet_elab::{
    Expr, FnDef, FnName, Op, Program, Stmt, Ty, TypedVar, Val, ir::Signedness,
    logic::semantic::Idx,
};
use z3::{SatResult, ast::{Bool, Int}};
use z3::Solver;

use crate::capabilities::CapabilityType::{self, Shrd, Uniq};

fn bool_or_or_false(values: &[Bool]) -> Bool {
    if values.is_empty() {
        Bool::from_bool(false)
    } else {
        Bool::or(values)
    }
}

fn bool_and_or_true(values: &[Bool]) -> Bool {
    if values.is_empty() {
        Bool::from_bool(true)
    } else {
        Bool::and(values)
    }
}

fn idx_to_z3(idx: &Idx, substitutions: &HashMap<String, Int>) -> Int {
    match idx {
        Idx::Const(value) => Int::from_i64(*value),
        Idx::Var(name) => substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| Int::new_const(name.clone())),
        Idx::Add(lhs, rhs) => Int::add(&[
            &idx_to_z3(lhs, substitutions),
            &idx_to_z3(rhs, substitutions),
        ]),
        Idx::Sub(lhs, rhs) => Int::sub(&[
            &idx_to_z3(lhs, substitutions),
            &idx_to_z3(rhs, substitutions),
        ]),
        Idx::Mul(lhs, rhs) => Int::mul(&[
            &idx_to_z3(lhs, substitutions),
            &idx_to_z3(rhs, substitutions),
        ]),
    }
}
fn inner_to_outer_array_map<T>(func: &FnDef<T>, args: &[Rc<Node>]) -> HashMap<String, String>{
    let mut map = HashMap::new();
    for (arg, param) in args.iter().zip(func.params.iter()){
        let inner_name = match &param.ty{
            Ty::RefShrd { .. } | Ty::RefUniq { .. } => &param.name,
            _ => continue
        };
        let outer_name: String = arg.var.as_ref().unwrap().name.clone();
        map.insert(inner_name.clone(), outer_name);
    }
    map
}
fn inner_to_outer_index_map<T>(func: &FnDef<T>, args: &[Rc<Node>]) -> HashMap<String, Int>{
    func.params
        .iter()
        .zip(args)
        .filter_map(|(param, arg)| match param.ty {
            Ty::Int(_) => Some((param.name.clone(), arg.to_z3_int()?)),
            _ => None,
        })
        .collect()
}
struct Node {
    op: NodeOp,
    var: Option<TypedVar>,
    parents: RefCell<Vec<Weak<Node>>>,
    fence_parents: RefCell<Vec<Weak<Node>>>
}
enum NodeOp {
    Constant(Val),
    Call(FnName, Vec<Rc<Node>>),
    TailCall(FnName, Vec<Rc<Node>>),
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
    Initial(HashMap<String, (Bool, Bool)>)
}
impl Node {
    fn arrays_accessed(&self) -> Vec<String>{
        match &self.op{
            NodeOp::Constant(_) => Vec::new(),
            NodeOp::Call(_, nodes) | NodeOp::TailCall(_, nodes) => {
                let mut vars: Vec<String> = Vec::new();
                for node in nodes{
                    let var = node.var.as_ref().unwrap();
                    let name = match &var.ty{
                        Ty::RefShrd { .. } | Ty::RefUniq { .. } => &var.name,
                        _=> continue
                    };
                    vars.push(name.clone());
                }
                vars
            },
            NodeOp::Write { array, .. } =>{
                vec![array.var.as_ref().unwrap().name.clone()]
            },
            NodeOp::Read { array, .. } => {
                vec![array.var.as_ref().unwrap().name.clone()]
            },
            NodeOp::Initial(map) => map.keys().cloned().collect(),
            _ => Vec::new()
        }
    }
    fn z3_capabilities_for_array(&self, cap_type: CapabilityType,array_name: &String,variable: &Int, functions: &HashMap<String, FnDef<TypedVar>>)->Option<Bool>{
        match &self.op{
            NodeOp::Call(fn_name, nodes) | NodeOp::TailCall(fn_name, nodes) => {
                let fndef =functions.get(&fn_name.0).unwrap();
                let mut props = Vec::new();
                let array_map = inner_to_outer_array_map(fndef, nodes);
                let index_map = inner_to_outer_index_map(fndef, nodes);
                for cap in fndef.caps.iter(){
                    if array_map.get(&cap.array).unwrap() != array_name{
                        continue;
                    }
                    
                    let Some(uniq) = (match cap_type{
                        CapabilityType::Shrd => &cap.shrd,
                        CapabilityType::Uniq => &cap.uniq,
                    }) else {continue};
                    for interval in uniq.iter(){
                        props.push(Bool::and(&[
                            variable.ge(idx_to_z3(&interval.lo, &index_map)),
                            variable.lt(idx_to_z3(&interval.hi, &index_map))
                        ]));
                    }
                }
                Some(bool_or_or_false(&props))
            },
            NodeOp::Write { array, idx, .. } => {
                if cap_type == CapabilityType::Shrd{
                    return None
                }
                if &array.var.as_ref().unwrap().name != array_name{
                    return None;
                }
                Some(variable.eq(idx.to_z3_int().unwrap()))
            },
            NodeOp::Read { array, idx } => {
                if cap_type == CapabilityType::Uniq{
                    return None
                }
                if &array.var.as_ref().unwrap().name != array_name{
                    return None;
                }
                Some(variable.eq(idx.to_z3_int().unwrap()))
            },
            NodeOp::Initial (map)=>{
                match cap_type{
                    Shrd => Some(map.get(array_name)?.0.clone()),
                    Uniq => Some(map.get(array_name)?.1.clone()),
                }
            }
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
            NodeOp::Variable | NodeOp::Initial(_) if fence => Some(Stmt::LetVal {
                var: TypedVar::new(
                    format!("_fence_dummy_{:x}", self as *const Node as usize),
                    Ty::Unit,
                ),
                val: Val::Unit,
                fence: true,
            }),
            NodeOp::Variable | NodeOp::Initial(_) | NodeOp::TailCall(..) => None,
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
            },
            NodeOp::Constant(_)
            | NodeOp::Initial(_)
            | NodeOp::Call(..)
            | NodeOp::TailCall(..)
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
                    _ => None,
                }?;
                Some(result.eq(value))
            }
            NodeOp::Constant(_)
            | NodeOp::Initial (_)
            | NodeOp::Call(..)
            | NodeOp::TailCall(..)
            | NodeOp::Write { .. }
            | NodeOp::Read { .. }
            | NodeOp::Variable => None,
        }
    }
}
fn collect_free_variables(
    stmts: &[Stmt<TypedVar>],
    tail_call: Option<(&FnName, &[TypedVar])>,
) -> Vec<Rc<Node>> {
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
    if let Some((_, args)) = tail_call {
        for arg in args {
            collect(arg);
        }
    }

    free_variables
}
struct Dag {
    nodes: Vec<Rc<Node>>,
    read_write_order: HashMap<String, Vec<Rc<Node>>>,
}
fn stmts_to_dag(
    stmts: &[Stmt<TypedVar>],
    functions: &HashMap<String, FnDef<TypedVar>>,
    initial_capabilities: HashMap<String,(Bool, Bool)>,
    tail_call: Option<(&FnName, &[TypedVar])>,
) -> Dag {
    let base_nodes = collect_free_variables(stmts, tail_call);
    let mut variable_map: HashMap<String, Rc<Node>> = base_nodes
        .iter()
        .filter_map(|node| {
            node.var
                .as_ref()
                .map(|var| (var.name.clone(), node.clone()))
        })
        .collect();
    let mut nodes = Vec::new();
    nodes.push(Rc::new(Node{
        op: NodeOp::Initial(initial_capabilities),
        var: None,
        parents: Default::default(),
        fence_parents: Default::default(),
    }));
    nodes.extend(base_nodes);
    let mut read_write_order: HashMap<String, Vec<Rc<Node>>> = HashMap::new();
    let NodeOp::Initial(initial_capabilities) = &nodes[0].op else {panic!("impossible")};
    for array in initial_capabilities.keys(){
        read_write_order.insert(array.clone(), vec![nodes[0].clone()]);
    }
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
            NodeOp::Constant(_)| NodeOp::Initial {..} | NodeOp::Variable => Vec::new(),
            NodeOp::Call(_, args) | NodeOp::TailCall(_, args) => args.clone(),
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
        match &node.op {
            NodeOp::Read { array, .. } | NodeOp::Write { array, .. } => {
                let array_name = array.var.as_ref().unwrap().name.clone();
                read_write_order
                    .entry(array_name)
                    .or_default()
                    .push(node.clone());
            }
            NodeOp::Call(function_name, arguments) => {
                let function = functions.get(&function_name.0).unwrap();
                let array_map = inner_to_outer_array_map(function, arguments);
                let mut seen_arrays = HashSet::new();
                for capability in &function.caps {
                    let array_name = array_map.get(&capability.array).unwrap();
                    if seen_arrays.insert(array_name.clone()) {
                        read_write_order
                            .entry(array_name.clone())
                            .or_default()
                            .push(node.clone());
                    }
                }
            }
            _ => {}
        }
        nodes.push(node);
    }
    if let Some((function_name, args)) = tail_call {
        let arguments: Vec<_> = args
            .iter()
            .map(|arg| variable_map.get(&arg.name).unwrap().clone())
            .collect();
        let tail_call = Rc::new(Node {
            op: NodeOp::TailCall(function_name.clone(), arguments),
            var: None,
            parents: Default::default(),
            fence_parents: Default::default(),
        });

        for node in &nodes {
            node.parents.borrow_mut().push(Rc::downgrade(&tail_call));
        }

        let function = functions.get(&function_name.0).unwrap();
        let NodeOp::TailCall(_, arguments) = &tail_call.op else {
            unreachable!()
        };
        let array_map = inner_to_outer_array_map(function, arguments);
        let mut seen_arrays = HashSet::new();
        for capability in &function.caps {
            let array_name = array_map.get(&capability.array).unwrap();
            if seen_arrays.insert(array_name.clone()) {
                read_write_order
                    .entry(array_name.clone())
                    .or_default()
                    .push(tail_call.clone());
            }
        }
        nodes.push(tail_call);
    }
    Dag {
        nodes,
        read_write_order,
    }
}
fn is_conflicting(uniq_caps1: Bool, uniq_caps2: Bool, shrd_caps1: Bool, shrd_caps2: Bool, solver: &Solver) -> bool {
    let a = [
        Bool::or(&[&uniq_caps1, &shrd_caps1]),
        uniq_caps2.clone()
    ];
    if solver.check_assumptions(&a) != SatResult::Unsat{
        return true;
    }
    let b = [
        Bool::or(&[uniq_caps2, shrd_caps2]),
        uniq_caps1
    ];
    if solver.check_assumptions(&b) != SatResult::Unsat{
        return true;
    }
    false
}

enum FenceOrNode{
    Fence,
    Node(Rc<Node>)
}
fn place_dependencies(
    read_write_order: &HashMap<String, Vec<Rc<Node>>>,
    assumptions: &Bool,
    functions: &HashMap<String, FnDef<TypedVar>>,
) {
    let solver = Solver::new();
    solver.assert(assumptions);
    for (array_name, access_order) in read_write_order.iter(){
        for i in 0..access_order.len(){
            for j in i+1..access_order.len(){
                let variable = Int::new_const("cool");
                let uniq_caps1 = access_order[i].z3_capabilities_for_array(Uniq, array_name, &variable, functions);
                let uniq_caps2 =access_order[j].z3_capabilities_for_array(Uniq, array_name, &variable, functions);
                if uniq_caps1.is_none() && uniq_caps2.is_none(){
                    continue;
                }
                let shrd_caps1 = access_order[i].z3_capabilities_for_array(Shrd, array_name, &variable, functions);
                let shrd_caps2 = access_order[j].z3_capabilities_for_array(Shrd, array_name, &variable, functions);
                let uniq_caps1 = uniq_caps1.unwrap_or(Bool::from_bool(false));
                let uniq_caps2 = uniq_caps2.unwrap_or(Bool::from_bool(false));
                
                let shrd_caps1 = shrd_caps1.unwrap_or(Bool::from_bool(false));
                let shrd_caps2 = shrd_caps2.unwrap_or(Bool::from_bool(false));

                if is_conflicting(uniq_caps1, uniq_caps2, shrd_caps1, shrd_caps2, &solver){
                    access_order[i]
                        .fence_parents
                        .borrow_mut()
                        .push(Rc::downgrade(&access_order[j]));
                }
            }
        }
    }
}

fn order_dag(dag: Dag, assumptions: &Bool, functions: &HashMap<String, FnDef<TypedVar>>) -> Vec<FenceOrNode> {
    let Dag {
        nodes,
        read_write_order,
    } = dag;

    place_dependencies(&read_write_order, assumptions, functions);

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
fn order_to_stmts(order: &Vec<FenceOrNode>) -> Vec<Stmt<TypedVar>>{
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
fn calculate_initial_capabilities(order: &Vec<FenceOrNode>, functions: &HashMap<String, FnDef<TypedVar>>) -> HashMap<String,(Bool, Bool)>{
    let mut uniq_map  = HashMap::new();
    let mut shrd_map  = HashMap::new();
    for stmt in order.iter().rev(){
        let FenceOrNode::Node(stmt) = stmt else {
            break
        };
        let arrays = stmt.arrays_accessed();
        let variable = Int::new_const("cool");


        for array in arrays{
            let uniq = stmt.z3_capabilities_for_array(Uniq, &array, &variable, functions);
            let shrd = stmt.z3_capabilities_for_array(Shrd, &array, &variable, functions);
            if let Some(shrd) = shrd{
                shrd_map.entry(array.clone()).or_insert_with(| |{ Vec::new()}).push(shrd);
            }
            if let Some(uniq) = uniq{
                uniq_map.entry(array).or_insert_with(| |{ Vec::new()}).push(uniq);
            }
        }
    }
    let mut combined = HashMap::new();
    for (k,v) in shrd_map{
        combined.entry(k).or_insert_with(||{(Vec::new(), Vec::new())}).0.extend(v);
    }
    for (k,v) in uniq_map{
        combined.entry(k).or_insert_with(||{(Vec::new(), Vec::new())}).1.extend(v);
    }
    combined
        .into_iter()
        .map(|(k, (a, b))| (k, (bool_or_or_false(&a), bool_or_or_false(&b))))
        .collect()
}
fn place_fences_expr(
    expr: &mut Expr<TypedVar>,
    assumptions: &Bool,
    initial_capabilities: HashMap<String,(Bool, Bool)>, //stores shrd,uniq of everything up to the beginning of the block
    functions: &HashMap<String, FnDef<TypedVar>>,
){
    let tail_call = match &expr.tail {
        wavelet_elab::Tail::TailCall { func, args } => Some((func, args.as_slice())),
        _ => None,
    };
    let dag = stmts_to_dag(
        &expr.stmts,
        functions,
        initial_capabilities,
        tail_call,
    );
    let code_as_z3: Vec<_> = dag.nodes.iter().filter_map(|node| node.to_z3()).collect();
    let code_as_z3 = bool_and_or_true(&code_as_z3);
    let assumptions = Bool::and(&[assumptions, &code_as_z3]);
    let order = order_dag(dag, &assumptions, functions);
    expr.stmts = order_to_stmts(&order);
    match &mut expr.tail{
        wavelet_elab::Tail::IfElse { cond, then_e, else_e } => {
            let initial_capabilities = calculate_initial_capabilities(&order, functions);
            let true_assumptions = Bool::and(&[&assumptions, &Bool::new_const(cond.name.clone())]);
            place_fences_expr(then_e, &true_assumptions, initial_capabilities.clone(),functions);
            let false_assumptions = Bool::and(&[&assumptions, &Bool::new_const(cond.name.clone()).not()]);
            place_fences_expr(else_e, &false_assumptions, initial_capabilities, functions);
        },
        wavelet_elab::Tail::TailCall { .. } => {}
        _ => {}
    }
}
fn place_fences_fn(
    func: &mut FnDef<TypedVar>,
    functions: &HashMap<String, FnDef<TypedVar>>,
){
    let mut assumptions = Vec::new();
    for x in &func.params{
        if let Ty::Int(Signedness::Unsigned) = &x.ty{
            assumptions.push(Int::new_const(x.name.clone()).ge(Int::from_i64(0)));
        }
    }
    let assumptions = bool_and_or_true(&assumptions);
    place_fences_expr(&mut func.body, &assumptions, HashMap::new(), functions);
}
pub fn place_fences(program: &mut Program<TypedVar>){
    let functions = program
        .defs
        .iter()
        .map(|function| (function.name.0.clone(), function.clone()))
        .collect();
    for func in &mut program.defs{
        place_fences_fn(func, &functions);
    }
}
