use std::{assert_eq, collections::{HashMap, HashSet}, env, error::Error, ffi::c_void, fs, io, vec};

use melior::{
    Context, IrRewriter, dialect::DialectRegistry, ir::{
        BlockLike, BlockRef, Module, OperationRef, Region, RegionLike, RegionRef, ShapedTypeLike, Type, TypeLike, Value, ValueLike, attribute::{BoolAttribute, DenseI64ArrayAttribute, FlatSymbolRefAttribute, IntegerAttribute, StringAttribute, TypeAttribute}, operation::{OperationLike, OperationResult}, r#type::{DimSize, FunctionType, IntegerType, MemRefType},
    }, utility::register_all_dialects,
};
mod capabilities;
mod loop_unswitching;
mod util;
mod fence_placement;
mod program_to_wavelet;
mod rename_variables;
mod type_program;
use capabilities::print_return_expressions;
use wavelet_elab::{Expr, FnDef, Op, Program, Stmt, Tail, Ty, TypedVar, UntypedVar, Val, ir::{ArrayLen, Signedness}};

use crate::{capabilities::{Capability, capability_constants, compute_capabilities, constant_fold_value, generate_expr, to_wavelet_capability}, program_to_wavelet::program_to_wavelet, rename_variables::rename_program_variables, util::{BlockIter, FreshWaveletNames, fresh_wavelet_name}};
fn module_to_wavelet<'c>(module: Module<'c>) -> Program<TypedVar> {
    let moduleref = module.as_operation();
    let mut untyped_program = Program { defs: Vec::new() };

    let Some(block) = moduleref.first_region().unwrap().first_block() else {
        return Program{
            defs: Default::default()
        };
    };
    let capability_map = compute_capabilities(&module);
    for func in BlockIter::new(block){
        function_to_wavelet(func, &mut untyped_program, &capability_map);
    }
    let mut program = type_program::type_program(&untyped_program).unwrap();
    rename_program_variables(&mut program);
    
    fence_placement::place_fences(&mut program);
    program
}


const generator: FreshWaveletNames = FreshWaveletNames::new();
fn operation_to_wavelet<'c, 'a>(
    operation: OperationRef<'c, 'a>,
    name: &str,
) -> Option<Option<Stmt<UntypedVar>>> {
    if name == "arith.constant" {
        return Some(constant_to_wavelet(operation));
    }

    if name == "memref.load" {
        let operands: Vec<_> = operation.operands().collect();
        if operands.len() != 2 {
            return None;
        }
        let array = UntypedVar(value_to_name(&operands[0]));
        let index = UntypedVar(value_to_name(&operands[1]));
        let len = wavelet_array_len(&operands[0])?;
        let result: Value<'_, '_> = operation.result(0).ok()?.into();

        return Some(Some(Stmt::LetOp {
            vars: vec![UntypedVar(value_to_name(&result))],
            op: wavelet_elab::Op::Load { array, index, len },
            fence: false,
        }));
    }

    if name == "memref.store" {
        let operands: Vec<_> = operation.operands().collect();
        if operands.len() != 3 {
            return None;
        }
        let value = UntypedVar(value_to_name(&operands[0]));
        let array = UntypedVar(value_to_name(&operands[1]));
        let index = UntypedVar(value_to_name(&operands[2]));
        let len = wavelet_array_len(&operands[1])?;

        return Some(Some(Stmt::LetOp {
            vars: vec![],
            op: wavelet_elab::Op::Store {
                array,
                index,
                value,
                len,
            },
            fence: false,
        }));
    }

    if name == "func.call" {
        let callee = FlatSymbolRefAttribute::try_from(
            operation
                .attribute("callee")
                .expect("func.call must have a callee attribute"),
        )
        .expect("func.call callee must be a flat symbol reference");
        let mut scalar_args = Vec::new();
        let mut array_args = Vec::new();
        for operand in operation.operands() {
            let argument = UntypedVar(value_to_name(&operand));
            match value_to_wavelet_ty(&operand) {
                Ty::RefShrd { .. } | Ty::RefUniq { .. } => array_args.push(argument),
                _ => scalar_args.push(argument),
            }
        }
        scalar_args.extend(array_args);

        assert!(
            operation.result_count() <= 1,
            "Wavelet does not support calls with multiple results"
        );
        let result = match operation.result(0) {
            Ok(result) => UntypedVar(value_to_name(&result.into())),
            Err(_) => UntypedVar(generator.fresh("_call_result")),
        };

        return Some(Some(Stmt::LetCall {
            vars: vec![result],
            func: wavelet_elab::FnName(callee.value().to_string()),
            args: scalar_args,
            fence: false,
        }));
    }
    if name == "memref.distinct_objects"{
        return Some(None);
    }
    let operands: Vec<_> = operation.operands().collect();
    if operands.len() != 2 {
        return None;
    }
    let binop = match name {
        "arith.addi" => Some((wavelet_elab::Op::<UntypedVar>::Add, false)),
        "arith.subi" => Some((wavelet_elab::Op::Sub, false)),
        "arith.muli" => Some((wavelet_elab::Op::Mul, false)),
        "arith.divsi" => Some((wavelet_elab::Op::Sdiv, false)),
        "arith.divui" => Some((wavelet_elab::Op::Udiv, false)),
        "arith.andi" if value_to_wavelet_ty(&operands[0]) == Ty::Bool => {
            Some((wavelet_elab::Op::And, false))
        }
        "arith.andi" => Some((wavelet_elab::Op::BitAnd, false)),
        "arith.ori" if value_to_wavelet_ty(&operands[0]) == Ty::Bool => {
            Some((wavelet_elab::Op::Or, false))
        }
        "arith.ori" => Some((wavelet_elab::Op::BitOr, false)),
        "arith.xori" if value_to_wavelet_ty(&operands[0]) == Ty::Bool => {
            Some((wavelet_elab::Op::NotEqual, false))
        }
        "arith.xori" => Some((wavelet_elab::Op::BitXor, false)),
        "arith.shli" => Some((wavelet_elab::Op::Shl, false)),
        "arith.shrsi" => Some((wavelet_elab::Op::Ashr, false)),
        "arith.shrui" => Some((wavelet_elab::Op::Lshr, false)),
        "arith.cmpi" => {
            let predicate = operation
                .attribute("predicate")
                .ok()
                .and_then(|attribute| IntegerAttribute::try_from(attribute).ok())
                .map(|attribute| attribute.value());
            match predicate {
                Some(0) => Some((wavelet_elab::Op::Equal, false)),
                Some(1) => Some((wavelet_elab::Op::NotEqual, false)),
                Some(2) => Some((wavelet_elab::Op::SignedLessThan, false)),
                Some(3) => Some((wavelet_elab::Op::SignedLessEqual, false)),
                Some(4) => Some((wavelet_elab::Op::SignedLessThan, true)),
                Some(5) => Some((wavelet_elab::Op::SignedLessEqual, true)),
                Some(6) => Some((wavelet_elab::Op::UnsignedLessThan, false)),
                Some(7) => Some((wavelet_elab::Op::UnsignedLessEqual, false)),
                Some(8) => Some((wavelet_elab::Op::UnsignedLessThan, true)),
                Some(9) => Some((wavelet_elab::Op::UnsignedLessEqual, true)),
                _ => None,
            }
        }
        _ => None,
    }?;

    let (op, reverse_operands) = binop;
    let mut vars: Vec<_> = operands
        .iter()
        .map(|operand| UntypedVar(value_to_name(operand)))
        .collect();
    if reverse_operands {
        vars.swap(0, 1);
    }
    vars.push(UntypedVar(value_to_name(
        &operation.result(0).ok()?.into(),
    )));

    Some(Some(Stmt::LetOp {
        vars,
        op,
        fence: false,
    }))
}

fn constant_to_wavelet(operation: OperationRef<'_, '_>) -> Option<Stmt<UntypedVar>> {
    let result = operation.result(0).ok()?;
    let attribute = operation.attribute("value").ok()?;
    let val = if value_to_wavelet_ty(&result.into()) == Ty::Bool {
        if let Ok(attribute) = BoolAttribute::try_from(attribute) {
            Val::Bool(attribute.value())
        } else {
            Val::Bool(IntegerAttribute::try_from(attribute).ok()?.value() != 0)
        }
    } else {
        Val::Int(IntegerAttribute::try_from(attribute).ok()?.value())
    };

    Some(Stmt::LetVal {
        var: UntypedVar(value_to_name(&result.into())),
        val,
        fence: false,
    })
}

fn value_to_wavelet_ty(value: &Value<'_, '_>) -> Ty {
    mlir_type_to_wavelet_ty(value.r#type())
}

fn wavelet_array_len(value: &Value<'_, '_>) -> Option<ArrayLen> {
    match value_to_wavelet_ty(value) {
        Ty::RefShrd { len, .. } | Ty::RefUniq { len, .. } => Some(len),
        _ => None,
    }
}

fn mlir_type_to_wavelet_ty(r#type: Type<'_>) -> Ty {
    if r#type.is_index() {
        return Ty::Int(Signedness::Signed);
    }

    if let Ok(integer_type) = IntegerType::try_from(r#type) {
        return if integer_type.width() == 1 {
            Ty::Bool
        } else if integer_type.is_unsigned() {
            Ty::Int(Signedness::Unsigned)
        } else {
            Ty::Int(Signedness::Signed)
        };
    }

    let memref_type = MemRefType::try_from(r#type)
        .unwrap_or_else(|_| panic!("unsupported MLIR type for Wavelet: {type}", type = r#type));
    assert_eq!(
        memref_type.rank(),
        1,
        "Wavelet only supports one-dimensional arrays"
    );
    let elem = mlir_type_to_wavelet_ty(memref_type.element());
    let len = match memref_type.dim_size(0).expect("memref dimension must exist") {
        DimSize::Static(size) => usize::try_from(size).expect("array length must fit in usize"),
        DimSize::Dynamic => panic!("Wavelet does not support dynamically sized arrays"),
    };

    Ty::RefUniq {
        elem: Box::new(elem),
        len: ArrayLen::Const(len),
    }
}

fn value_to_name(value: &Value<'_, '_>) -> String {
    let t= format!("v{:p}",value.to_raw().ptr);
    t
}
fn function_to_name(function: &OperationRef<'_, '_>) -> String {
    let quoted_name = StringAttribute::try_from(
        function
            .attribute("sym_name")
            .expect("func.func must have a sym_name attribute"),
    )
    .expect("func.func sym_name must be a string attribute")
    .to_string();
    assert!(
        quoted_name.len() >= 2,
        "func.func sym_name must include surrounding quotation marks"
    );
    quoted_name[1..quoted_name.len() - 1].to_string()
}
fn for_loop_to_function_name(for_loop: &OperationRef<'_, '_>) -> String{
    let t= format!("f{:p}",for_loop.to_raw().ptr);
    t
}
fn if_to_function_name(if_statement: &OperationRef<'_, '_>) -> String {
    format!("if_{:p}", if_statement.to_raw().ptr)
}
fn find_free_variables<'c, 'a>(block: BlockRef<'c, 'a>) -> Vec<Value<'c, 'a>> {
    fn collect_definitions<'c, 'a>(
        block: BlockRef<'c, 'a>,
        definitions: &mut HashSet<*const c_void>,
    ) {
        for operation in BlockIter::new(block) {
            for result in operation.results() {
                definitions.insert(result.to_raw().ptr);
            }
            for region in operation.regions() {
                let mut nested_block = region.first_block();
                while let Some(current) = nested_block {
                    for index in 0..current.argument_count() {
                        definitions.insert(current.argument(index).unwrap().to_raw().ptr);
                    }
                    collect_definitions(current, definitions);
                    nested_block = current.next_in_region();
                }
            }
        }
    }

    fn collect_uses<'c, 'a>(
        block: BlockRef<'c, 'a>,
        definitions: &HashSet<*const c_void>,
        seen: &mut HashSet<*const c_void>,
        free_variables: &mut Vec<Value<'c, 'a>>,
    ) {
        for operation in BlockIter::new(block) {
            for operand in operation.operands() {
                let value = operand.to_raw().ptr;
                if !definitions.contains(&value) && seen.insert(value) {
                    free_variables.push(operand);
                }
            }
            for region in operation.regions() {
                let mut nested_block = region.first_block();
                while let Some(current) = nested_block {
                    collect_uses(current, definitions, seen, free_variables);
                    nested_block = current.next_in_region();
                }
            }
        }
    }

    let mut definitions = HashSet::new();
    collect_definitions(block, &mut definitions);

    let mut free_variables = Vec::new();
    collect_uses(
        block,
        &definitions,
        &mut HashSet::new(),
        &mut free_variables,
    );
    free_variables
}

fn function_to_wavelet<'c, 'a>(func: OperationRef<'c, 'a>, program: &mut Program<UntypedVar>, func_map: &HashMap<* mut c_void, Vec<Capability<'c, 'a>>>){
    let block = func.region(0).unwrap().first_block().unwrap();
    let alias_information = block.first_operation();
    let mut arguments = Vec::new();
    let mut alloc_arrays = Vec::new();

    for argument_index in 0..block.argument_count() {
        let value: Value<'_, '_> = block.argument(argument_index).unwrap().into();
        if MemRefType::try_from(value.r#type()).is_ok() {
            continue;
        }
        arguments.push(TypedVar {
            name: value_to_name(&value),
            ty: value_to_wavelet_ty(&value),
        });
    }

    if let Some(first_line) = alias_information{
        let ident = first_line.name();
        let opname = ident.as_string_ref().as_str().unwrap();
        if opname == "memref.distinct_objects"{
            let alloc_array_indices = first_line
                .attribute("alloc_arrays")
                .ok()
                .map(|attribute| {
                    DenseI64ArrayAttribute::try_from(attribute)
                        .expect("alloc_arrays must be an array<i64> attribute")
                });

            for (result_index, arr) in first_line.results().enumerate(){
                let value = arr.into();
                let name = value_to_name(&value);

                if alloc_array_indices.is_some_and(|indices| {
                    (0..indices.len()).any(|index| {
                        indices.element(index).unwrap() == result_index as i64
                    })
                }) {
                    alloc_arrays.push(name.clone());
                }

                arguments.push(TypedVar {
                    name,
                    ty: value_to_wavelet_ty(&value),
                });
            }
        }
    }
    let name = function_to_name(&func);
    let caps = func_map.get(&func.to_raw().ptr).unwrap();
    let caps = to_wavelet_capability(caps);

    let type_attribute =
      TypeAttribute::try_from(func.attribute("function_type").unwrap()).unwrap();
    let function_type  = FunctionType::try_from(type_attribute.value()).unwrap();
    if function_type.result_count() > 1{
        panic!("does not support functions with multiple return types")
    }
    let returns  = function_type.result(0)
        .map_or(Ty::Unit, |t| mlir_type_to_wavelet_ty(t));

    let body = block_to_wavelet(block, program, None,func_map);
    let wavelet_func = wavelet_elab::FnDef{
        name: wavelet_elab::FnName(name),
        params: arguments, 
        alloc_arrays,
        caps, 
        returns, 
        body
    };
    program.add_fn(wavelet_func);
}
fn value_to_typed_var(value: &Value<'_, '_>) -> TypedVar{
    TypedVar { 
        name: value_to_name(value), 
        ty: value_to_wavelet_ty(value) 
    }
}
#[derive(Debug, Clone)]
enum ForLoopParameterValue {
    Constant(i64),
    Variable(TypedVar),
}
fn for_loop_parameter_values<'c, 'a>(
    for_loop: OperationRef<'c, 'a>,
) -> (ForLoopParameterValue, ForLoopParameterValue) {
    fn parameter_value<'c, 'a>(
        for_loop: OperationRef<'c, 'a>,
        operand_index: usize,
    ) -> ForLoopParameterValue {
        let value = for_loop.operand(operand_index).unwrap();
        match generate_expr(value, Some(for_loop)).and_then(|expression| expression.constant_propagate()) {
            Some(constant) => ForLoopParameterValue::Constant(constant),
            None => ForLoopParameterValue::Variable(value_to_typed_var(&value)),
        }
    }

    (parameter_value(for_loop, 1), parameter_value(for_loop, 2))
}
struct TailCallInformation {
    function_name: wavelet_elab::FnName,
    parameters: Vec<TypedVar>,
    iteration_argument: UntypedVar,
    next_iteration: UntypedVar,
    carried_argument: Option<UntypedVar>,
}

impl TailCallInformation {
    fn tail(&self, yielded: Option<UntypedVar>) -> Tail<UntypedVar> {
        let arguments = self
            .parameters
            .iter()
            .map(|parameter| {
                if parameter.name == self.iteration_argument.0 {
                    self.next_iteration.clone()
                } else if self
                    .carried_argument
                    .as_ref()
                    .is_some_and(|argument| parameter.name == argument.0)
                {
                    yielded
                        .clone()
                        .expect("loop with an iter_arg must yield a value")
                } else {
                    UntypedVar(parameter.name.clone())
                }
            })
            .collect();
        Tail::TailCall {
            func: self.function_name.clone(),
            args: arguments,
        }
    }
}
fn partition_captured_values(values: &[Value<'_, '_>]) -> (Vec<TypedVar>, Vec<Stmt<UntypedVar>>) {
    let mut parameters = Vec::new();
    let mut constants = Vec::new();
    for value in values {
        if let Some(constant) = constant_fold_value(*value) {
            let val = if value_to_wavelet_ty(value) == Ty::Bool {
                Val::Bool(constant != 0)
            } else {
                Val::Int(constant)
            };
            constants.push(Stmt::LetVal {
                var: UntypedVar(value_to_name(value)),
                val,
                fence: false,
            });
        } else {
            parameters.push(value_to_typed_var(value));
        }
    }
    (parameters, constants)
}

fn for_loop_function_captures<'c, 'a>(
    for_loop: OperationRef<'c, 'a>,
    upper_bound: &ForLoopParameterValue,
    step: &ForLoopParameterValue,
) -> (Vec<TypedVar>, Vec<Stmt<UntypedVar>>) {
    let block = for_loop
        .first_region()
        .unwrap()
        .first_block()
        .unwrap();
    let free_variables = find_free_variables(block);
    let (mut parameters, constants) = partition_captured_values(&free_variables);

    for parameter_value in [upper_bound, step] {
        if let ForLoopParameterValue::Variable(parameter) = parameter_value
            && !parameters
                .iter()
                .any(|existing| existing.name == parameter.name)
        {
            parameters.push(parameter.clone());
        }
    }
    for argument_index in 0..block.argument_count() {
        let argument: Value<'_, '_> = block.argument(argument_index).unwrap().into();
        let parameter = value_to_typed_var(&argument);
        if !parameters
            .iter()
            .any(|existing| existing.name == parameter.name)
        {
            parameters.push(parameter);
        }
    }

    (parameters, constants)
}
fn if_to_wavelet<'c, 'a>(
    if_statement: OperationRef<'c, 'a>,
    program: &mut Program<UntypedVar>,
    cap_map: &HashMap<*mut c_void, Vec<Capability<'c, 'a>>>,
) -> Stmt<UntypedVar> {
    assert!(
        if_statement.result_count() <= 1,
        "Wavelet does not support scf.if with multiple results"
    );

    let condition = if_statement.operand(0).unwrap();
    let mut parameter_values = vec![condition];
    let mut seen = HashSet::from([condition.to_raw().ptr]);
    for region in if_statement.regions() {
        if let Some(block) = region.first_block() {
            for value in find_free_variables(block) {
                if seen.insert(value.to_raw().ptr) {
                    parameter_values.push(value);
                }
            }
        }
    }
    let (parameters, constant_statements) = partition_captured_values(&parameter_values);
    let arguments = parameters
        .iter()
        .map(|parameter| UntypedVar(parameter.name.clone()))
        .collect();

    let return_value = if_statement.result(0).ok();
    let returns = return_value.map_or(Ty::Unit, |result| {
        let value: Value<'_, '_> = result.into();
        value_to_wavelet_ty(&value)
    });
    let function_name = wavelet_elab::FnName(if_to_function_name(&if_statement));
    let condition = UntypedVar(value_to_name(&condition));
    let then_block = if_statement.region(0).unwrap().first_block().unwrap();
    let then_e = block_to_wavelet(then_block, program, None, cap_map);
    let else_e = if_statement
        .region(1)
        .ok()
        .and_then(|region| region.first_block())
        .map(|else_block| block_to_wavelet(else_block, program, None, cap_map))
        .unwrap_or_else(|| {
            let unit = UntypedVar(generator.fresh("_if_unit"));
            Expr {
                stmts: vec![Stmt::LetVal {
                    var: unit.clone(),
                    val: Val::Unit,
                    fence: false,
                }],
                tail: Tail::RetVar(unit),
            }
        });
    let caps = to_wavelet_capability(
        cap_map
            .get(&if_statement.to_raw().ptr)
            .expect("missing capabilities for scf.if"),
    );
    program.add_fn(FnDef {
        name: function_name.clone(),
        params: parameters,
        alloc_arrays: Vec::new(),
        caps,
        returns,
        body: Expr {
            stmts: constant_statements,
            tail: Tail::IfElse {
                cond: condition,
                then_e: Box::new(then_e),
                else_e: Box::new(else_e),
            },
        },
    });

    let result = return_value.map_or_else(
        || UntypedVar(generator.fresh("_if_result")),
        |result| UntypedVar(value_to_name(&result.into())),
    );
    Stmt::LetCall {
        vars: vec![result],
        func: function_name,
        args: arguments,
        fence: false,
    }
}
fn for_to_wavelet<'c, 'a>(for_loop: OperationRef<'c, 'a>, program: &mut Program<UntypedVar>, cap_map: &HashMap<* mut c_void, Vec<Capability<'c, 'a>>>) ->  Stmt<UntypedVar>{
    let block = for_loop
        .first_region()
        .unwrap()
        .first_block()
        .unwrap();
    let (upper_bound, step) = for_loop_parameter_values(for_loop);
    let (params, mut body_stmts) =
        for_loop_function_captures(for_loop, &upper_bound, &step);
    let caps = to_wavelet_capability(
        cap_map
            .get(&for_loop.to_raw().ptr)
            .unwrap()
    );
    assert!(
        for_loop.result_count() <= 1,
        "Wavelet does not support scf.for with multiple iter_args"
    );
    let return_value = for_loop.result(0).ok();
    let returns = return_value.map_or(Ty::Unit, |result| {
        let value: Value<'_, '_> = result.into();
        value_to_wavelet_ty(&value)
    });
    let function_name = wavelet_elab::FnName(for_loop_to_function_name(&for_loop));
    let iteration_argument = UntypedVar(value_to_name(&block.argument(0).unwrap().into()));
    let carried_argument = (block.argument_count() == 2).then(|| {
        UntypedVar(value_to_name(&block.argument(1).unwrap().into()))
    });
    let upper_bound = match upper_bound {
        ForLoopParameterValue::Constant(value) => {
            let variable = UntypedVar(generator.fresh("_upper_bound"));
            body_stmts.push(Stmt::LetVal {
                var: variable.clone(),
                val: Val::Int(value),
                fence: false,
            });
            variable
        }
        ForLoopParameterValue::Variable(parameter) => UntypedVar(parameter.name),
    };
    let step = match step {
        ForLoopParameterValue::Constant(value) => {
            let variable = UntypedVar(generator.fresh("_step"));
            body_stmts.push(Stmt::LetVal {
                var: variable.clone(),
                val: Val::Int(value),
                fence: false,
            });
            variable
        }
        ForLoopParameterValue::Variable(parameter) => UntypedVar(parameter.name),
    };
    let condition = UntypedVar(generator.fresh("_loop_condition"));
    body_stmts.push(Stmt::LetOp {
        vars: vec![
            iteration_argument.clone(),
            upper_bound,
            condition.clone(),
        ],
        op: Op::SignedLessThan,
        fence: false,
    });
    let next_iteration = UntypedVar(generator.fresh("_next_iteration"));
    let tail_call = TailCallInformation {
        function_name: function_name.clone(),
        parameters: params.clone(),
        iteration_argument: iteration_argument.clone(),
        next_iteration: next_iteration.clone(),
        carried_argument: carried_argument.clone(),
    };
    let mut inner_body = block_to_wavelet(block, program, Some(&tail_call),cap_map);
    inner_body.stmts.insert(0, Stmt::LetOp {
        vars: vec![iteration_argument.clone(), step, next_iteration],
        op: Op::Add,
        fence: false,
    });
    let else_e = match &carried_argument {
        Some(argument) => Expr {
            stmts: Vec::new(),
            tail: Tail::RetVar(argument.clone()),
        },
        None => {
            let unit = UntypedVar(generator.fresh("_loop_unit"));
            Expr {
                stmts: vec![Stmt::LetVal {
                    var: unit.clone(),
                    val: Val::Unit,
                    fence: false,
                }],
                tail: Tail::RetVar(unit),
            }
        }
    };
    let body = Expr {
        stmts: body_stmts,
        tail: Tail::IfElse {
            cond: condition,
            then_e: Box::new(inner_body),
            else_e: Box::new(else_e),
        },
    };

    let iter_arg = block.argument(1)
        .ok()
        .map(|f| {
            let v: Value<'_, '_> = f.into(); 
            value_to_name(&v)
    });
    let default_iter_arg = for_loop.operand(3).ok();
    let lower_bound = for_loop.operand(0).unwrap();
    let untyped_params: Vec<UntypedVar> = params.iter().map(|p|{
        if p.name == iteration_argument.0 {
            UntypedVar(value_to_name(&lower_bound))
        }else if let Some(name) = iter_arg.as_ref() && &p.name == name {
            UntypedVar(value_to_name(default_iter_arg.as_ref().unwrap()))
        }else {
            UntypedVar(p.name.clone())
        }
    }
    ).collect();
    let func: FnDef<UntypedVar> = FnDef{
        name: function_name,
        params: params,
        alloc_arrays: Vec::new(),
        caps,
        returns,
        body,
    };

    program.add_fn(func);
    let dummy_var = UntypedVar(fresh_wavelet_name("if_"));
    let return_var = return_value.map_or(dummy_var, |f| UntypedVar(value_to_name(&f.into())));
    let for_stmt: Stmt<UntypedVar> = Stmt::LetCall { 
        vars: vec![return_var], 
        func: wavelet_elab::FnName(for_loop_to_function_name(&for_loop)), 
        args: untyped_params, 
        fence: false
    };
    for_stmt
}
fn block_to_wavelet<'c, 'a>(
    block: BlockRef<'c, 'a>,
    program: &mut Program<UntypedVar>,
    tail_call: Option<&TailCallInformation>,
    cap_map: &HashMap<* mut c_void, Vec<Capability<'c, 'a>>>
) -> wavelet_elab::Expr<UntypedVar>{
    let mut stmts = Vec::new();
    let mut tail = None;
    for operation in BlockIter::new(block) {
        let ident = operation.name();
        let name = ident.as_string_ref().as_str().unwrap();
        if name == "func.return" || name == "scf.yield"{
            let yielded = operation
                .operand(0)
                .ok()
                .map(|value| UntypedVar(value_to_name(&value)));
            if name == "scf.yield" && tail_call.is_some() {
                tail = Some(tail_call.unwrap().tail(yielded));
            } else {
                let returned = yielded.unwrap_or_else(|| {
                    let unit = UntypedVar("_unit_ret".to_string());
                    stmts.push(Stmt::LetVal {
                        var: unit.clone(),
                        val: Val::Unit,
                        fence: false,
                    });
                    unit
                });
                tail = Some(Tail::RetVar(returned));
            }
            break;
        }else if name == "scf.if" {
            let yield_operation = operation.next_in_block().filter(|next| {
                next.name().as_string_ref().as_str().unwrap() == "scf.yield"
            });
            let directly_yielded = yield_operation.is_some_and(|yield_operation| {
                match yield_operation.operand(0) {
                    Ok(value) => OperationResult::try_from(value)
                        .is_ok_and(|result| result.owner().to_raw().ptr == operation.to_raw().ptr),
                    Err(_) => operation.result_count() == 0,
                }
            });
            if !directly_yielded {
                stmts.push(if_to_wavelet(operation, program, cap_map));
                continue;
            }
            assert!(
                operation.result_count() <= 1,
                "Wavelet does not support scf.if with multiple results"
            );
            let condition = UntypedVar(value_to_name(&operation.operand(0).unwrap()));
            let then_block = operation.region(0).unwrap().first_block().unwrap();
            let then_e = block_to_wavelet(then_block, program, tail_call, cap_map);
            let else_e = operation
                .region(1)
                .ok()
                .and_then(|region| region.first_block())
                .map(|else_block| block_to_wavelet(else_block, program, tail_call, cap_map))
                .unwrap_or_else(|| {
                    let unit = UntypedVar("_unit_ret".to_string());
                    Expr {
                        stmts: tail_call.is_none().then(|| Stmt::LetVal {
                            var: unit.clone(),
                            val: Val::Unit,
                            fence: false,
                        }).into_iter().collect(),
                        tail: tail_call.map_or_else(
                            || Tail::RetVar(unit),
                            |information| information.tail(None),
                        ),
                    }
                });
            tail = Some(Tail::IfElse {
                cond: condition,
                then_e: Box::new(then_e),
                else_e: Box::new(else_e),
            });
            break;
        }else if operation.region_count() == 0 {
            let wavelet_op = operation_to_wavelet(operation, name);
            if wavelet_op.is_none(){
                panic!("unsupported operation {}", operation)
            }
            if let Some(wavelet_op) = wavelet_op.unwrap(){
                stmts.push(wavelet_op);
            }

        }else if name == "scf.for"{
            stmts.push(for_to_wavelet(operation, program, cap_map));
        }
    }
    
    wavelet_elab::Expr{
        stmts,
        tail: tail.unwrap(),
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = env::args_os();
    let _ = args.next();
    let input_path = args.next().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "usage: scftowavelet <input.mlir> <output.mlir>",
        )
    })?;
    let output_path = args.next().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "usage: scftowavelet <input.mlir> <output.mlir>",
        )
    })?;
    let source = fs::read_to_string(&input_path)?;

    let registry = DialectRegistry::new();
    register_all_dialects(&registry);

    let context = Context::new_with_registry(&registry, false);
    for dialect in ["memref", "arith", "func", "scf"] {
        context.get_or_load_dialect(dialect);
    }

    let mut module = Module::parse(&context, &source).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!(
                "failed to parse MLIR file: {}",
                input_path.to_string_lossy()
            ),
        )
    })?;


    
    // print_return_expressions(&module);
    // loop_unswitching::loop_unswitch(&context, &mut module);
    // let mut program = Program { defs: Vec::new() };
    // let mut func = module.as_operation().first_region().unwrap().first_block().unwrap().first_operation().unwrap();
    // let mut cap_map = compute_capabilities(&module);
    // capability_constants(&mut cap_map);
    // function_to_wavelet(func, &mut program, &cap_map);
    // rename_program_variables(&mut program);

    let mut wavelet_program = module_to_wavelet(module);
    let output_program = program_to_wavelet(&wavelet_program);

    fs::write(output_path, output_program)?;
    // if !module.as_operation().verify() {
    //     println!("failed to verify");
    // }
    Ok(())
}

#[cfg(test)]
mod tests;
