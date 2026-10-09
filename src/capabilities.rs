use std::{
    collections::{HashMap, VecDeque}, ffi::c_void, fmt::{self, Display, Formatter}, rc::Rc,
};

use melior::ir::{
    BlockLike, BlockRef, Module, OperationRef, RegionLike, ShapedTypeLike, Value, ValueLike, attribute::{FlatSymbolRefAttribute, IntegerAttribute, StringAttribute}, block::BlockArgument, operation::{OperationLike, OperationResult, WalkOrder, WalkResult}, r#type::{DimSize, MemRefType},
};
use wavelet_elab::{
    ir::Signedness,
    logic::{cap::CapPattern, region::{Interval, Region}, semantic::Idx},
};
use z3::{
    SatResult, Solver, ast::{self, Ast, Bool},
};

use crate::{functions_in_call_order, value_to_name};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CapabilityType {
    Shrd,
    Uniq,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CapabilityOp {
    Add,
    Sub,
    Mult,
}

#[derive(Debug, Clone)]
pub(super) enum CapabilityExpr<'c, 'a> {
    BinOp {
        operation: CapabilityOp,
        operands: (Rc<CapabilityExpr<'c, 'a>>, Rc<CapabilityExpr<'c, 'a>>), //inclusive range
    },
    Constant(i64),
    Variable {
        value: Value<'c, 'a>,
        signedness: Signedness,
    },
    Blackbox {
        value: Value<'c, 'a>,
        signedness: Signedness,
    },
}

impl<'c, 'a> CapabilityExpr<'c, 'a> {
    /// Replaces parameters positionally; a referenced None poisons this expression.
    pub(super) fn substitute(
        &self,
        parameters: &[Value<'c, 'a>],
        substitutions: &[Option<CapabilityExpr<'c, 'a>>],
    ) -> anyhow::Result<Option<Self>> {
        if parameters.len() != substitutions.len() {
            return Err(anyhow::anyhow!("parameter and substitution counts must match"));
        }
        Ok(match self {
            Self::Variable { value, .. } | Self::Blackbox { value, .. } => parameters
                .iter()
                .position(|parameter| parameter == value)
                .map_or_else(|| Some(self.clone()), |index| substitutions[index].clone()),
            Self::BinOp { operation, operands } => operands.0
                .substitute(parameters, substitutions)?
                .zip(operands.1.substitute(parameters, substitutions)?)
                .map(|(lhs, rhs)| Self::BinOp {
                    operation: *operation,
                    operands: (Rc::new(lhs), Rc::new(rhs)),
                }),
            Self::Constant(_) => Some(self.clone()),
        })
    }

    pub(super) fn to_wavelet_idx<'d, 'b>(
        &self
    ) -> Idx {
        match self {
            CapabilityExpr::Constant(n) => Idx::Const(*n),
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => {
                let lhs = operands.0.to_wavelet_idx();
                let rhs = operands.1.to_wavelet_idx();
                match operation {
                    CapabilityOp::Add => Idx::Add(Box::new(lhs), Box::new(rhs)),
                    CapabilityOp::Sub => Idx::Sub(Box::new(lhs), Box::new(rhs)),
                    CapabilityOp::Mult => Idx::Mul(Box::new(lhs), Box::new(rhs)),
                }
            }
            CapabilityExpr::Variable { value, .. } => {
                Idx::Var(crate::value_to_name(value))
            }
            CapabilityExpr::Blackbox { value, .. } => Idx::Var(crate::value_to_name(value)),
        }
    }
    pub(super) fn simplified(&self) -> CapabilityExpr<'c, 'a> {
        if let Some(value) = self.constant_propagate() {
            return CapabilityExpr::Constant(value);
        }

        let CapabilityExpr::BinOp {
            operation,
            operands,
        } = self
        else {
            return self.clone();
        };

        let lhs = operands.0.simplified();
        let rhs = operands.1.simplified();

        if *operation == CapabilityOp::Add {
            if let (
                CapabilityExpr::BinOp {
                    operation: CapabilityOp::Add,
                    operands: lhs_operands,
                },
                CapabilityExpr::Constant(rhs_value),
            ) = (&lhs, &rhs)
            {
                if let CapabilityExpr::Constant(lhs_value) = lhs_operands.1.as_ref() {
                    if let Some(value) = lhs_value.checked_add(*rhs_value) {
                        return CapabilityExpr::BinOp {
                            operation: CapabilityOp::Add,
                            operands: (
                                Rc::clone(&lhs_operands.0),
                                Rc::new(CapabilityExpr::Constant(value)),
                            ),
                        };
                    }
                }
            }
        }

        match (operation, &lhs, &rhs) {
            (CapabilityOp::Add, _, CapabilityExpr::Constant(0))
            | (CapabilityOp::Sub, _, CapabilityExpr::Constant(0))
            | (CapabilityOp::Mult, _, CapabilityExpr::Constant(1)) => lhs,
            (CapabilityOp::Add, CapabilityExpr::Constant(0), _)
            | (CapabilityOp::Mult, CapabilityExpr::Constant(1), _) => rhs,
            (CapabilityOp::Mult, _, CapabilityExpr::Constant(0))
            | (CapabilityOp::Mult, CapabilityExpr::Constant(0), _) => CapabilityExpr::Constant(0),
            _ => CapabilityExpr::BinOp {
                operation: *operation,
                operands: (Rc::new(lhs), Rc::new(rhs)),
            },
        }
    }

    fn precedence(&self) -> u8 {
        match self {
            CapabilityExpr::BinOp {
                operation: CapabilityOp::Add | CapabilityOp::Sub,
                ..
            } => 1,
            CapabilityExpr::BinOp {
                operation: CapabilityOp::Mult,
                ..
            } => 2,
            CapabilityExpr::Constant(_)
            | CapabilityExpr::Variable { .. }
            | CapabilityExpr::Blackbox { .. } => 3,
        }
    }

    fn fmt_compact(&self, formatter: &mut Formatter<'_>, minimum_precedence: u8) -> fmt::Result {
        let precedence = self.precedence();
        let parenthesize = precedence < minimum_precedence;
        if parenthesize {
            write!(formatter, "(")?;
        }

        match self {
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => {
                operands.0.fmt_compact(formatter, precedence)?;
                let symbol = match operation {
                    CapabilityOp::Add => "+",
                    CapabilityOp::Sub => "-",
                    CapabilityOp::Mult => "*",
                };
                write!(formatter, " {symbol} ")?;
                let rhs_precedence = if *operation == CapabilityOp::Sub {
                    precedence + 1
                } else {
                    precedence
                };
                operands.1.fmt_compact(formatter, rhs_precedence)?;
            }
            CapabilityExpr::Constant(value) => write!(formatter, "{value}")?,
            CapabilityExpr::Variable { .. } => write!(formatter, "i")?,
            CapabilityExpr::Blackbox { value, .. } => {
                write!(formatter, "{}", compact_value_name(*value))?
            }
        }

        if parenthesize {
            write!(formatter, ")")?;
        }
        Ok(())
    }

    fn substitute_variable(
        &self,
        variable_replacement: &CapabilityExpr<'c, 'a>,
    ) -> CapabilityExpr<'c, 'a> {
        match self {
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => CapabilityExpr::BinOp {
                operation: *operation,
                operands: (
                    Rc::new(operands.0.substitute_variable(variable_replacement)),
                    Rc::new(operands.1.substitute_variable(variable_replacement)),
                ),
            },
            CapabilityExpr::Variable { .. } => variable_replacement.clone(),
            CapabilityExpr::Constant(_) | CapabilityExpr::Blackbox { .. } => self.clone(),
        }
    }

    fn expand_blackboxes(
        &self,
        parent_for_loop: Option<OperationRef<'c, 'a>>,
    ) -> Option<CapabilityExpr<'c, 'a>> {
        match self {
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => Some(CapabilityExpr::BinOp {
                operation: *operation,
                operands: (
                    Rc::new(operands.0.expand_blackboxes(parent_for_loop)?),
                    Rc::new(operands.1.expand_blackboxes(parent_for_loop)?),
                ),
            }),
            CapabilityExpr::Blackbox { value, .. } => match parent_for_loop {
                Some(for_loop) => generate_expr(*value, Some(for_loop)),
                None => Some(self.clone()),
            },
            CapabilityExpr::Constant(_) | CapabilityExpr::Variable { .. } => Some(self.clone()),
        }
    }

    pub(super) fn promote(
        &self,
        variable_replacement: &CapabilityExpr<'c, 'a>,
        parent_for_loop: Option<OperationRef<'c, 'a>>,
    ) -> Option<CapabilityExpr<'c, 'a>> {
        self.substitute_variable(variable_replacement)
            .expand_blackboxes(parent_for_loop)
    }

    pub(super) fn constant_propagate(&self) -> Option<i64> {
        match self {
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => {
                let lhs = operands.0.constant_propagate()?;
                let rhs = operands.1.constant_propagate()?;

                match operation {
                    CapabilityOp::Add => lhs.checked_add(rhs),
                    CapabilityOp::Sub => lhs.checked_sub(rhs),
                    CapabilityOp::Mult => lhs.checked_mul(rhs),
                }
            }
            CapabilityExpr::Constant(value) => Some(*value),
            CapabilityExpr::Variable { .. } | CapabilityExpr::Blackbox { .. } => None,
        }
    }

    pub(super) fn to_z3(&self) -> ast::Int {
        match self {
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => {
                let lhs = operands.0.to_z3();
                let rhs = operands.1.to_z3();

                match operation {
                    CapabilityOp::Add => ast::Int::add(&[&lhs, &rhs]),
                    CapabilityOp::Sub => ast::Int::sub(&[&lhs, &rhs]),
                    CapabilityOp::Mult => ast::Int::mul(&[&lhs, &rhs]),
                }
            }
            CapabilityExpr::Constant(value) => ast::Int::from_i64(*value),
            CapabilityExpr::Variable { value, .. }
            | CapabilityExpr::Blackbox { value, .. } => value_to_z3(value),
        }
    }

    fn iteration_variable_to_z3(&self) -> Option<ast::Int> {
        match self {
            CapabilityExpr::BinOp { operands, .. } => operands
                .0
                .iteration_variable_to_z3()
                .or_else(|| operands.1.iteration_variable_to_z3()),
            CapabilityExpr::Variable { value, .. } => Some(value_to_z3(value)),
            CapabilityExpr::Constant(_) | CapabilityExpr::Blackbox { .. } => None,
        }
    }

}

fn value_to_z3(value: &Value<'_, '_>) -> ast::Int {
    ast::Int::new_const(format!("value_{:x}", value.to_raw().ptr as usize))
}

impl Display for CapabilityExpr<'_, '_> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        self.simplified().fmt_compact(formatter, 0)
    }
}

fn compact_value_name(value: Value<'_, '_>) -> String {
    if let Ok(argument) = BlockArgument::try_from(value) {
        return format!("arg{}", argument.argument_number());
    }

    let printed = value.to_string();
    printed
        .split_once(" = ")
        .map_or(printed.as_str(), |(name, _)| name)
        .trim()
        .to_string()
}

#[derive(Debug, Clone)]
pub(super) struct Capability<'c, 'a> {
    pub(super) array: Value<'c, 'a>,
    pub(super) capability_type: CapabilityType,
    pub(super) capability_expr: Option<(CapabilityExpr<'c, 'a>, CapabilityExpr<'c, 'a>)>, // None means "poison" which takes the entire bounds of the array
}

impl<'c, 'a> Capability<'c, 'a> {
    /// Substitutes the array and both inclusive bounds, preserving poisoned regions.
    pub(super) fn substitute(
        &self,
        parameters: &[Value<'c, 'a>],
        substitutions: &[Option<CapabilityExpr<'c, 'a>>],
    ) -> anyhow::Result<Self> {
        if parameters.len() != substitutions.len() {
            return Err(anyhow::anyhow!("parameter and substitution counts must match"));
        }
        let array = match parameters.iter().position(|parameter| *parameter == self.array) {
            Some(index) => match &substitutions[index] {
                Some(CapabilityExpr::Variable { value, .. } | CapabilityExpr::Blackbox { value, .. })
                    if MemRefType::try_from(value.r#type()).is_ok() => *value,
                _ => return Err(anyhow::anyhow!("capability array substitution must be a memref value")),
            },
            None => self.array,
        };
        Ok(Self {
            array,
            capability_type: self.capability_type,
            capability_expr: match &self.capability_expr {
                Some((start, end)) => start.substitute(parameters, substitutions)?
                    .zip(end.substitute(parameters, substitutions)?),
                None => None,
            },
        })
    }
}

pub(super) fn capability_constants<'c, 'a>(
    capability_map: &mut HashMap<*mut c_void, Vec<Capability<'c, 'a>>>,
) {
    fn replace_constants<'c, 'a>(expression: &CapabilityExpr<'c, 'a>) -> CapabilityExpr<'c, 'a> {
        let replaced = match expression {
            CapabilityExpr::BinOp {
                operation,
                operands,
            } => CapabilityExpr::BinOp {
                operation: *operation,
                operands: (
                    Rc::new(replace_constants(&operands.0)),
                    Rc::new(replace_constants(&operands.1)),
                ),
            },
            CapabilityExpr::Blackbox { value, .. } => constant_fold_value(*value)
                .map(CapabilityExpr::Constant)
                .unwrap_or_else(|| expression.clone()),
            CapabilityExpr::Constant(_) | CapabilityExpr::Variable { .. } => expression.clone(),
        };
        replaced.simplified()
    }

    for capabilities in capability_map.values_mut() {
        for capability in capabilities {
            if let Some((start, end)) = &mut capability.capability_expr {
                *start = replace_constants(start);
                *end = replace_constants(end);
            }
        }
    }
}

pub(super) fn to_wavelet_capability(
    capabilities: &[Capability<'_, '_>],
) -> Vec<CapPattern> {
    struct PatternIntervals {
        array: String,
        size: usize,
        uniq: Vec<Interval>,
        shrd: Vec<Interval>,
    }

    let mut pattern_intervals: Vec<PatternIntervals> = Vec::new();

    for capability in capabilities {
        let memref_type = MemRefType::try_from(capability.array.r#type()).unwrap();
        let size = match memref_type
            .dim_size(0)
            .unwrap()
        {
            DimSize::Static(size) => {
                usize::try_from(size).unwrap()
            }
            DimSize::Dynamic => panic!("Wavelet does not support dynamically sized arrays"),
        };
        let array = value_to_name(&capability.array);
        let interval = match &capability.capability_expr {
            Some((start, end)) => {
                let end_exclusive = CapabilityExpr::BinOp {
                    operation: CapabilityOp::Add,
                    operands: (
                        Rc::new(end.clone()),
                        Rc::new(CapabilityExpr::Constant(1)),
                    ),
                };
                Interval::bounded(
                    start.simplified().to_wavelet_idx(),
                    end_exclusive.simplified().to_wavelet_idx(),
                )
            }
            None => Interval::bounded(Idx::Const(0), Idx::from_usize(size)),
        };

        let pattern = match pattern_intervals
            .iter_mut()
            .find(|pattern| pattern.array == array)
        {
            Some(pattern) => pattern,
            None => {
                pattern_intervals.push(PatternIntervals {
                    array,
                    size,
                    uniq: Vec::new(),
                    shrd: Vec::new(),
                });
                pattern_intervals.last_mut().unwrap()
            }
        };
        let intervals = match capability.capability_type {
            CapabilityType::Shrd => &mut pattern.shrd,
            CapabilityType::Uniq => &mut pattern.uniq,
        };
        intervals.push(interval);
    }

    pattern_intervals
        .into_iter()
        .map(|pattern| CapPattern {
            array: pattern.array,
            len: wavelet_elab::ir::ArrayLen::Const(pattern.size),
            uniq: (!pattern.uniq.is_empty()).then(|| Region::from_intervals(pattern.uniq)),
            shrd: (!pattern.shrd.is_empty()).then(|| Region::from_intervals(pattern.shrd)),
        })
        .collect()
}
impl Display for Capability<'_, '_> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        let kind = match self.capability_type {
            CapabilityType::Shrd => "shrd",
            CapabilityType::Uniq => "uniq",
        };
        let array = compact_value_name(self.array);
        match &self.capability_expr {
            Some((start, end)) => write!(formatter, "{array}: {kind} @ {start}..{end}"),
            None => write!(formatter, "{array}: {kind} @ *"),
        }
    }
}

pub(super) fn format_capabilities(capabilities: &[Capability<'_, '_>]) -> String {
    capabilities
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

pub(super) fn has_iteration_variable(expr: &CapabilityExpr<'_, '_>) -> bool {
    match expr {
        CapabilityExpr::BinOp { operands, .. } => {
            has_iteration_variable(&operands.0) || has_iteration_variable(&operands.1)
        }
        CapabilityExpr::Variable { .. } => true,
        CapabilityExpr::Constant(_) | CapabilityExpr::Blackbox { .. } => false,
    }
}

fn for_loop_signedness(for_loop: OperationRef<'_, '_>) -> Signedness {
    if for_loop.attribute("unsignedCmp").is_ok() {
        Signedness::Unsigned
    } else {
        Signedness::Signed
    }
}

fn find_parent_for<'c, 'a>(operation: OperationRef<'c, 'a>) -> Option<OperationRef<'c, 'a>> {
    let mut parent = operation.block()?.parent_operation()?;

    loop {
        let ident = parent.name();
        let name = ident.as_string_ref().as_str().ok()?;

        if name == "scf.for" {
            return Some(parent);
        }

        parent = parent.block()?.parent_operation()?;
    }
}

pub(super) fn find_parent_iterator<'c, 'a>(
    operation: OperationRef<'c, 'a>,
) -> Option<Value<'c, 'a>> {
    let parent_for = find_parent_for(operation)?;
    let body = parent_for.first_region()?.first_block()?;
    Some(body.argument(0).ok()?.into())
}

fn block_is_inside_operation(block: BlockRef<'_, '_>, ancestor: OperationRef<'_, '_>) -> bool {
    let mut parent = block.parent_operation();

    while let Some(operation) = parent {
        if operation.to_raw().ptr == ancestor.to_raw().ptr {
            return true;
        }
        parent = operation.block().and_then(|block| block.parent_operation());
    }

    false
}

pub(super) fn generate_expr<'c, 'a>(
    value: Value<'c, 'a>,
    target_for_loop: Option<OperationRef<'c, 'a>>,
) -> Option<CapabilityExpr<'c, 'a>>
where
    'c: 'a,
{
    generate_expr_helper(value, target_for_loop, false)
}

pub(super) fn constant_fold_value(value: Value<'_, '_>) -> Option<i64> {
    let operation = OperationResult::try_from(value).ok()?.owner();
    let ident = operation.name();
    let name = ident.as_string_ref().as_str().ok()?;

    if name == "arith.constant" {
        let attr = operation.attribute("value").ok()?;
        return Some(IntegerAttribute::try_from(attr).ok()?.value());
    }

    let lhs = constant_fold_value(operation.operand(0).ok()?)?;
    let rhs = constant_fold_value(operation.operand(1).ok()?)?;
    match name {
        "arith.addi" => lhs.checked_add(rhs),
        "arith.subi" => lhs.checked_sub(rhs),
        "arith.muli" => lhs.checked_mul(rhs),
        _ => None,
    }
}

fn generate_expr_helper<'c, 'a>(
    value: Value<'c, 'a>,
    target_for_loop: Option<OperationRef<'c, 'a>>,
    expand_external_arithmetic: bool,
) -> Option<CapabilityExpr<'c, 'a>>
where
    'c: 'a,
{
    if let Ok(argument) = BlockArgument::try_from(value) {
        let owner = argument.owner();

        if let Some(for_loop) = target_for_loop {
            let loop_body = for_loop.first_region()?.first_block()?;
            let iterator: Value<'c, 'a> = loop_body.argument(0).ok()?.into();

            if iterator.to_raw().ptr == value.to_raw().ptr {
                return Some(CapabilityExpr::Variable {
                    value,
                    signedness: for_loop_signedness(for_loop),
                });
            }

            if block_is_inside_operation(owner, for_loop) {
                return None;
            }
        }

        return Some(CapabilityExpr::Blackbox {
            value,
            signedness: Signedness::Signed,
        });
    }
    let operation = OperationResult::try_from(value).ok()?;
    let operation = operation.owner();

    let is_defined_inside_target = target_for_loop.is_some_and(|for_loop| {
        operation
            .block()
            .is_some_and(|block| block_is_inside_operation(block, for_loop))
    });

    let ident = operation.name();
    let name = ident.as_string_ref().as_str().unwrap();
    // Call arguments must express supported arithmetic in terms of the caller's
    // parameters, even when the defining operation is outside the target loop.
    let expand_external = expand_external_arithmetic
        && matches!(name, "arith.addi" | "arith.subi" | "arith.muli");
    if !is_defined_inside_target && !expand_external {
        return Some(match constant_fold_value(value) {
            Some(value) => CapabilityExpr::Constant(value),
            None => CapabilityExpr::Blackbox {
                value,
                signedness: Signedness::Signed,
            },
        });
    }

    let binop = match name {
        "arith.constant" => {
            let attr = operation.attribute("value").ok()?;
            let value = IntegerAttribute::try_from(attr).ok()?.value();
            return Some(CapabilityExpr::Constant(value));
        }
        "arith.addi" => CapabilityOp::Add,
        "arith.subi" => CapabilityOp::Sub,
        "arith.muli" => CapabilityOp::Mult,
        _ => return None,
    };
    let operands = (
        Rc::new(generate_expr_helper(
            operation.operand(0).unwrap(),
            target_for_loop,
            expand_external_arithmetic,
        )?),
        Rc::new(generate_expr_helper(
            operation.operand(1).unwrap(),
            target_for_loop,
            expand_external_arithmetic,
        )?),
    );
    Some(CapabilityExpr::BinOp {
        operation: binop,
        operands,
    })
}

pub(super) fn print_return_expressions(module: &Module<'_>) {
    module
        .as_operation()
        .walk(WalkOrder::PreOrder, |operation| {
            let ident = operation.name();
            let name = ident.as_string_ref().as_str().unwrap();

            if name == "func.return" {
                let target_for_loop = find_parent_for(operation);
                for value in operation.operands() {
                    if let Some(expression) = generate_expr(value, target_for_loop) {
                        println!("{expression}");
                    }
                }
            }

            WalkResult::Advance
        });
}

fn push_capability<'c, 'a>(
    capabilities: &mut Vec<Capability<'c, 'a>>,
    capability: Capability<'c, 'a>,
) -> bool {
    let array = capability.array.to_raw().ptr;
    let is_poisoned = capability.capability_expr.is_none();

    if capabilities.iter().any(|existing| {
        existing.array.to_raw().ptr == array
            && existing.capability_expr.is_none()
            && existing.capability_type == CapabilityType::Uniq
    }) {
        return false;
    }

    if is_poisoned && capability.capability_type == CapabilityType::Uniq {
        capabilities.retain(|existing| existing.array.to_raw().ptr != array);
        capabilities.push(capability);
        return true;
    }

    if capability.capability_type == CapabilityType::Shrd
        && capabilities.iter().any(|existing| {
            existing.array.to_raw().ptr == array
                && existing.capability_expr.is_none()
                && existing.capability_type == CapabilityType::Shrd
        })
    {
        return false;
    }

    if is_poisoned && capability.capability_type == CapabilityType::Shrd {
        capabilities.retain(|existing| {
            existing.array.to_raw().ptr != array || existing.capability_type == CapabilityType::Uniq
        });
    }

    capabilities.push(capability);
    true
}
/// Keeps source parameter order, using distinct_objects results for array parameters.
pub(super) fn function_parameter_values<'c, 'a>(function: OperationRef<'c, 'a>) -> Vec<Value<'c, 'a>> {
    let body = function.first_region().unwrap().first_block().unwrap();
    let mut parameters: Vec<Value<'c, 'a>> = (0..body.argument_count())
        .map(|index| body.argument(index).unwrap().into())
        .collect();
    if let Some(distinct) = body.first_operation().filter(|operation| {
        operation.name().as_string_ref().as_str().unwrap() == "memref.distinct_objects"
    }) {
        for parameter in &mut parameters {
            if MemRefType::try_from(parameter.r#type()).is_ok() {
                if let Some(index) = distinct.operands().position(|operand| operand == *parameter) {
                    *parameter = distinct.result(index).unwrap().into();
                }
            }
        }
    }
    parameters
}

pub(super) fn compute_capabilities<'c, 'a>(module: &'c Module<'c>) -> anyhow::Result<HashMap<* mut c_void, Vec<Capability<'c, 'a>>>>
where 'c: 'a
{
    let mut hashmap = HashMap::new();
    let functions = functions_in_call_order(module.body())?;
    let mut functions_by_name = HashMap::new();
    for func in &functions {
        let name = StringAttribute::try_from(func.attribute("sym_name")?)?
            .value()
            .to_owned();
        functions_by_name.insert(name, *func);
    }
    for func in functions {
        let mut caps = Vec::new();
        let parameters = function_parameter_values(func);
        block_capabilities(
            func.region(0).unwrap().first_block().unwrap(), 
            &mut hashmap, &mut caps, &functions_by_name, &parameters
        );
        hashmap.insert(func.to_raw().ptr, coalesce_capabilities(caps));
    }
    capability_constants(&mut hashmap);
    Ok(hashmap)
}
pub(super) fn block_capabilities<'c, 'a, 'b>(
    block: BlockRef<'c, 'a>,
    capability_map: &mut HashMap<* mut c_void, Vec<Capability<'c, 'a>>>,
    capabilities: &mut Vec<Capability<'c, 'a>>,
    functions_by_name: &HashMap<String, OperationRef<'c, 'a>>,
    parameters: &[Value<'c, 'a>],
) where
    'c: 'a,
{
    println!(
        "[block_capabilities] enter block with {} propagated capabilities",
        capabilities.len()
    );
    let mut current_opt = block.first_operation();
    while let Some(current) = current_opt {
        let ident = current.name();
        let name = ident.as_string_ref().as_str().unwrap();
        println!("[block_capabilities] visiting {name}");
        if name == "func.call"{
            let callee = FlatSymbolRefAttribute::try_from(current.attribute("callee").unwrap())
                .unwrap();
            let func_op = functions_by_name.get(callee.value()).unwrap();
            let callee_parameters = function_parameter_values(*func_op);
            let target_for_loop = find_parent_for(current);
            let substitutions: Vec<_> = current.operands().map(|value| {
                // Array identity is known even when scalar index expressions are not.
                if MemRefType::try_from(value.r#type()).is_ok() {
                    Some(CapabilityExpr::Blackbox { value, signedness: Signedness::Signed })
                } else {
                    generate_expr_helper(value, target_for_loop, true)
                }
            }).collect();
            let inner_function_capabilities = capability_map.get(&func_op.to_raw().ptr)
                .cloned()
                .unwrap_or_else(|| {
                    // A self-call has no completed summary yet. Require full-array
                    // unique capabilities rather than omitting recursive accesses.
                    callee_parameters.iter().filter_map(|value| {
                        MemRefType::try_from(value.r#type()).ok().map(|_| Capability {
                            array: *value,
                            capability_type: CapabilityType::Uniq,
                            capability_expr: None,
                        })
                    }).collect()
                });
            for capability in inner_function_capabilities {
                let translated = capability.substitute(&callee_parameters, &substitutions)
                    .expect("call capability substitution failed");
                push_capability(capabilities, translated);
            }
        }else if name == "memref.load" {
            let array = current.operand(0).unwrap();
            let idx = current.operand(1).unwrap();
            let capability_expr = generate_expr(idx, find_parent_for(current));
            if push_capability(
                capabilities,
                Capability {
                    array,
                    capability_type: CapabilityType::Shrd,
                    capability_expr: capability_expr.map(|x| (x.clone(), x)),
                },
            ) {
                println!(
                    "[block_capabilities] added load capability: {}",
                    capabilities.last().unwrap()
                );
            } else {
                println!("[block_capabilities] load capability already covered");
            }
        } else if name == "memref.store" {
            let array = current.operand(1).unwrap();
            let idx = current.operand(2).unwrap();
            let capability_expr = generate_expr(idx, find_parent_for(current));
            if push_capability(
                capabilities,
                Capability {
                    array,
                    capability_type: CapabilityType::Uniq,
                    capability_expr: capability_expr.map(|x| (x.clone(), x)),
                },
            ) {
                println!(
                    "[block_capabilities] added store capability: {}",
                    capabilities.last().unwrap()
                );
            } else {
                println!("[block_capabilities] store capability already covered");
            }
        } else if name == "scf.if" {
            println!("[block_capabilities] descending into scf.if");
            let mut if_capabilities = Vec::new();
            for region in current.regions() {
                if let Some(sub_block) = region.first_block() {
                    block_capabilities(sub_block, capability_map, &mut if_capabilities, functions_by_name, parameters);
                }
            }
            let if_capabilities = coalesce_capabilities(if_capabilities);
            capability_map.insert(current.to_raw().ptr, if_capabilities.clone());
            for capability in if_capabilities {
                push_capability(capabilities, capability);
            }
        } else if name == "scf.for" {
            println!("[block_capabilities] collecting inner scf.for capabilities");
            let inner_block = current.first_region().unwrap().first_block().unwrap();
            let mut inner_capabilities = vec![];
            block_capabilities(inner_block, capability_map, &mut inner_capabilities, functions_by_name, parameters);
            println!(
                "[block_capabilities] scf.for produced {} inner capabilities",
                inner_capabilities.len()
            );
            let lower_bound_var = current.operand(0).unwrap();
            let upper_bound_var = current.operand(1).unwrap();
            let step_var = current.operand(2).unwrap();
            let lower_bound = generate_expr(lower_bound_var, Some(current)).map(Rc::new);
            let upper_bound = generate_expr(upper_bound_var, Some(current)).map(Rc::new);
            let parent_for_loop = find_parent_for(current);
            let is_range_poisoned = lower_bound.is_none() || upper_bound.is_none();
            let step =
                generate_expr(step_var, Some(current)).and_then(|step| step.constant_propagate());
            let iterator: Value<'c, 'a> = inner_block.argument(0).unwrap().into();
            let iteration = CapabilityExpr::Variable {
                value: iterator,
                signedness: for_loop_signedness(current),
            };
            let mut loop_capabilities = Vec::new();

            for capability in inner_capabilities {
                let Capability {
                    array,
                    capability_type,
                    capability_expr,
                } = capability;

                match capability_expr {
                    Some((start, end))
                        if has_iteration_variable(&start) || has_iteration_variable(&end) =>
                    {
                        if is_range_poisoned || step.is_none() {
                            push_capability(
                                &mut loop_capabilities,
                                Capability {
                                    array,
                                    capability_type,
                                    capability_expr: None,
                                },
                            );
                            println!(
                                "[block_capabilities] poisoned loop capability because a loop bound is unknown"
                            );
                            continue;
                        }

                        let pattern = z3_for_loop_viability(&start, &end, &upper_bound_var);
                        println!("[block_capabilities] loop access pattern: {pattern:?}");

                        for loop_capability in loop_function_capabilities(
                            array,
                            capability_type,
                            &start,
                            &end,
                            upper_bound.as_ref().unwrap(),
                            &iteration,
                            pattern,
                            current,
                        ) {
                            push_capability(&mut loop_capabilities, loop_capability);
                        }
                    }
                    capability_expr => {
                        push_capability(
                            &mut loop_capabilities,
                            Capability {
                                array,
                                capability_type,
                                capability_expr,
                            },
                        );
                    }
                }
            }

            let loop_capabilities = coalesce_capabilities(loop_capabilities);
            capability_map.insert(current.to_raw().ptr, loop_capabilities.clone());

            for loop_capability in loop_capabilities {
                let Capability {
                    array,
                    capability_type,
                    capability_expr,
                } = loop_capability;
                let capability_expr = match capability_expr {
                    Some((start, end))
                        if has_iteration_variable(&start) || has_iteration_variable(&end) =>
                    {
                        let lower_bound = lower_bound.as_ref().unwrap();
                        start
                            .promote(lower_bound, parent_for_loop)
                            .zip(end.promote(lower_bound, parent_for_loop))
                    }
                    capability_expr => capability_expr,
                };
                let enclosing_capability = Capability {
                    array,
                    capability_type,
                    capability_expr,
                };
                let inserted = push_capability(capabilities, enclosing_capability);
                println!(
                    "[block_capabilities] pushed coalesced loop capability; inserted={inserted}"
                );
            }
        }
        
        current_opt = current.next_in_block();
    }

    println!(
        "[block_capabilities] exit block with {} propagated capabilities: [{}]",
        capabilities.len(),
        format_capabilities(capabilities)
    );
}

fn loop_function_capabilities<'c, 'a>(
    array: Value<'c, 'a>,
    capability_type: CapabilityType,
    x: &CapabilityExpr<'c, 'a>,
    y: &CapabilityExpr<'c, 'a>,
    upper_bound_exclusive: &CapabilityExpr<'c, 'a>,
    iteration: &CapabilityExpr<'c, 'a>,
    pattern: Pattern,
    for_loop: OperationRef<'c, 'a>,
) -> Vec<Capability<'c, 'a>> {
    if pattern == Pattern::Poison {
        return vec![Capability {
            array,
            capability_type,
            capability_expr: None,
        }];
    }

    let upper_bound = CapabilityExpr::BinOp {
        operation: CapabilityOp::Sub,
        operands: (
            Rc::new(upper_bound_exclusive.clone()),
            Rc::new(CapabilityExpr::Constant(1)),
        ),
    };

    let promoted = match pattern {
        Pattern::Increasing => x
            .promote(iteration, Some(for_loop))
            .zip(y.promote(&upper_bound, Some(for_loop))),
        Pattern::Decreasing => x
            .promote(&upper_bound, Some(for_loop))
            .zip(y.promote(iteration, Some(for_loop))),
        Pattern::Poison => unreachable!(),
    };

    let Some((capability_start, capability_end)) = promoted else {
        return vec![Capability {
            array,
            capability_type,
            capability_expr: None,
        }];
    };

    vec![Capability {
        array,
        capability_type,
        capability_expr: Some((capability_start, capability_end)),
    }]
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Pattern {
    Increasing,
    Decreasing,
    Poison,
}

pub(super) fn coalesce_capabilities<'c, 'a>(
    capabilities: Vec<Capability<'c, 'a>>,
) -> Vec<Capability<'c, 'a>> {
    let mut group_indices = HashMap::new();
    let mut capabilities_by_array: Vec<Vec<Capability<'c, 'a>>> = Vec::new();

    for capability in capabilities {
        let array = capability.array.to_raw().ptr;
        let group_index = *group_indices.entry(array).or_insert_with(|| {
            capabilities_by_array.push(Vec::new());
            capabilities_by_array.len() - 1
        });
        capabilities_by_array[group_index].push(capability);
    }

    capabilities_by_array
        .into_iter()
        .flat_map(coalesce_capabilities_by_array)
        .collect()
}
fn solver_proves(solver: &Solver, proposition: &Bool) -> bool {
    solver.check_assumptions(&[proposition.not()]) == SatResult::Unsat
}

fn capability_bounds<'c, 'a>(
    capability: &Capability<'c, 'a>,
) -> (CapabilityExpr<'c, 'a>, CapabilityExpr<'c, 'a>) {
    if let Some(bounds) = &capability.capability_expr {
        return bounds.clone();
    }

    let memref_type = MemRefType::try_from(capability.array.r#type()).unwrap();
    let size = match memref_type.dim_size(0).unwrap() {
        DimSize::Static(size) => i64::try_from(size).unwrap(),
        DimSize::Dynamic => panic!("Wavelet does not support dynamically sized arrays"),
    };
    (
        CapabilityExpr::Constant(0),
        CapabilityExpr::Constant(size - 1),
    )
}

fn capability_is_always_empty(capability: &Capability<'_, '_>) -> bool {
    let (start_expr, end_expr) = capability_bounds(capability);
    let mut assumptions = z3_assumptions(&start_expr);
    assumptions.extend(z3_assumptions(&end_expr));

    let solver = Solver::new();
    solver.assert(Bool::and(&assumptions));
    solver.check() == SatResult::Sat
        && solver_proves(&solver, &end_expr.to_z3().lt(start_expr.to_z3()))
}

fn offset_capability_expr<'c, 'a>(
    expression: &CapabilityExpr<'c, 'a>,
    operation: CapabilityOp,
) -> CapabilityExpr<'c, 'a> {
    CapabilityExpr::BinOp {
        operation,
        operands: (
            Rc::new(expression.clone()),
            Rc::new(CapabilityExpr::Constant(1)),
        ),
    }
    .simplified()
}

fn shared_capability<'c, 'a>(
    array: Value<'c, 'a>,
    start: CapabilityExpr<'c, 'a>,
    end: CapabilityExpr<'c, 'a>,
) -> Capability<'c, 'a> {
    Capability {
        array,
        capability_type: CapabilityType::Shrd,
        capability_expr: Some((start, end)),
    }
}

fn unique_capability<'c, 'a>(
    array: Value<'c, 'a>,
    start: CapabilityExpr<'c, 'a>,
    end: CapabilityExpr<'c, 'a>,
) -> Capability<'c, 'a> {
    Capability {
        array,
        capability_type: CapabilityType::Uniq,
        capability_expr: Some((start, end)),
    }
}

pub(super) fn coalesce_pair<'c, 'a>(
    shrd: Capability<'c, 'a>,
    uniq: &mut Capability<'c, 'a>,
) -> (
    Option<Capability<'c, 'a>>,
    Option<Capability<'c, 'a>>,
    Option<Capability<'c, 'a>>,
) {
    debug_assert_eq!(shrd.array.to_raw().ptr, uniq.array.to_raw().ptr);
    debug_assert_eq!(shrd.capability_type, CapabilityType::Shrd);
    debug_assert_eq!(uniq.capability_type, CapabilityType::Uniq);

    if capability_is_always_empty(&shrd) {
        return (None, None, None);
    }
    if capability_is_always_empty(uniq) {
        return (Some(shrd), None, None);
    }

    let (shrd_start_expr, shrd_end_expr) = capability_bounds(&shrd);
    let (uniq_start_expr, uniq_end_expr) = capability_bounds(uniq);
    let mut assumptions = z3_assumptions(&shrd_start_expr);
    assumptions.extend(z3_assumptions(&shrd_end_expr));
    assumptions.extend(z3_assumptions(&uniq_start_expr));
    assumptions.extend(z3_assumptions(&uniq_end_expr));

    let shrd_start = shrd_start_expr.to_z3();
    let shrd_end = shrd_end_expr.to_z3();
    let uniq_start = uniq_start_expr.to_z3();
    let uniq_end = uniq_end_expr.to_z3();

    let solver = Solver::new();
    solver.assert(Bool::and(&assumptions));
    solver.assert(shrd_start.le(&shrd_end));
    solver.assert(uniq_start.le(&uniq_end));
    if solver.check() != SatResult::Sat {
        return (Some(shrd), None, None);
    }
    if solver_proves(&solver, &shrd_end.lt(&uniq_start))
        || solver_proves(&solver, &uniq_end.lt(&shrd_start))
    {
        return (Some(shrd), None, None);
    }

    let uniq_starts_before = solver_proves(&solver, &uniq_start.le(&shrd_start));
    let shrd_starts_before = solver_proves(&solver, &shrd_start.le(&uniq_start));
    let uniq_ends_after = solver_proves(&solver, &shrd_end.le(&uniq_end));
    let shrd_ends_after = solver_proves(&solver, &uniq_end.le(&shrd_end));
    let array = shrd.array;
    println!("{} {} {} {} {} {}", shrd, uniq,uniq_starts_before,shrd_starts_before,uniq_ends_after,shrd_ends_after);
    match (
        uniq_starts_before,
        shrd_starts_before,
        uniq_ends_after,
        shrd_ends_after,
    ) {
        (true, _, true, _) => (None, None, None),
        (true, _, _, true) => (
            Some(shared_capability(
                array,
                offset_capability_expr(&uniq_end_expr, CapabilityOp::Add),
                shrd_end_expr,
            )),
            None,
            None,
        ),
        (_, true, true, _) => (
            Some(shared_capability(
                array,
                shrd_start_expr,
                offset_capability_expr(&uniq_start_expr, CapabilityOp::Sub),
            )),
            None,
            None,
        ),
        (_, true, _, true) => (
            Some(shared_capability(
                array.clone(),
                shrd_start_expr,
                offset_capability_expr(&uniq_start_expr, CapabilityOp::Sub),
            )),
            Some(shared_capability(
                array,
                offset_capability_expr(&uniq_end_expr, CapabilityOp::Add),
                shrd_end_expr,
            )),
            None,
        ),
        (_, true, false, false) => (
            Some(shared_capability(
                array.clone(),
                shrd_start_expr,
                offset_capability_expr(&uniq_start_expr, CapabilityOp::Sub),
            )),
            None,
            Some(unique_capability(
                array,
                offset_capability_expr(&uniq_end_expr, CapabilityOp::Add),
                shrd_end_expr,
            )),
        ),
        _ => (
            None,
            None,
            Some(unique_capability(array, shrd_start_expr, shrd_end_expr)),
        ),
    }
}

pub(super) fn coalesce_capabilities_by_array<'c, 'a>(
    capabilities: Vec<Capability<'c, 'a>>,
) -> Vec<Capability<'c, 'a>> {
    let (mut shrd_capabilities, uniq_capabilities): (Vec<_>, Vec<_>) = capabilities
        .into_iter()
        .filter(|capability| !capability_is_always_empty(capability))
        .partition(|capability| capability.capability_type == CapabilityType::Shrd);
    let mut pending_uniq = VecDeque::from(uniq_capabilities);
    let mut coalesced_capabilities = Vec::new();

    while let Some(mut uniq) = pending_uniq.pop_front() {
        let mut remaining_shrd = Vec::new();
        for shrd in shrd_capabilities {
            let (first, second, generated_uniq) = coalesce_pair(shrd, &mut uniq);
            remaining_shrd.extend(
                first
                    .into_iter()
                    .chain(second)
                    .filter(|capability| !capability_is_always_empty(capability)),
            );
            pending_uniq.extend(
                generated_uniq
                    .into_iter()
                    .filter(|capability| !capability_is_always_empty(capability)),
            );
        }
        shrd_capabilities = remaining_shrd;
        coalesced_capabilities.push(uniq);
    }

    coalesced_capabilities.extend(shrd_capabilities);
    coalesced_capabilities
}

pub(super) fn z3_assumptions<'c, 'a>(
    expression: &CapabilityExpr<'c, 'a>,
) -> Vec<Bool> {
    match expression {
        CapabilityExpr::BinOp { operands, .. } => {
            let mut assumptions = z3_assumptions(&operands.0);
            assumptions.extend(z3_assumptions(&operands.1));
            assumptions
        }
        CapabilityExpr::Variable {
            signedness: Signedness::Unsigned,
            ..
        }
        | CapabilityExpr::Blackbox {
            signedness: Signedness::Unsigned,
            ..
        } => vec![expression.to_z3().ge(ast::Int::from_i64(0))],
        CapabilityExpr::Constant(_)
        | CapabilityExpr::Variable {
            signedness: Signedness::Signed,
            ..
        }
        | CapabilityExpr::Blackbox {
            signedness: Signedness::Signed,
            ..
        } => Vec::new(),
    }
}
pub(super) fn z3_for_loop_viability<'c, 'a>(
    start: &CapabilityExpr<'c, 'a>,
    end: &CapabilityExpr<'c, 'a>,
    for_loop_end_value: &Value<'c, 'a>,
) -> Pattern {
    let iteration_variable = start
        .iteration_variable_to_z3()
        .or_else(|| end.iteration_variable_to_z3());
    let for_loop_end = value_to_z3(for_loop_end_value);
    let x = start.to_z3();
    let y = end.to_z3();

    let (x_1, y_1) = if let Some(iteration_variable) = &iteration_variable {
        let next_iteration = ast::Int::add(&[iteration_variable, &ast::Int::from_i64(1)]);
        (
            x.substitute(&[(iteration_variable, &next_iteration)]),
            y.substitute(&[(iteration_variable, &next_iteration)]),
        )
    } else {
        (x.clone(), y.clone())
    };

    let mut assumptions = z3_assumptions(start);
    assumptions.extend(z3_assumptions(end));
    if let Some(iteration_variable) = &iteration_variable {
        assumptions.push(iteration_variable.lt(&for_loop_end));
    }
    let assumption_refs = assumptions.iter().collect::<Vec<_>>();
    let assumption = Bool::and(&assumption_refs);
    let growing_counterexample =
        Bool::and(&[&assumption, &Bool::and(&[x.le(&x_1), y.le(&y_1)]).not()]);

    let solver = Solver::new();
    solver.assert(growing_counterexample);
    if solver.check() == SatResult::Unsat {
        return Pattern::Increasing;
    }
    let shrinking_counterexample =
        Bool::and(&[&assumption, &Bool::and(&[x.ge(&x_1), y.ge(&y_1)]).not()]);
    let solver = Solver::new();
    solver.assert(shrinking_counterexample);
    if solver.check() == SatResult::Unsat {
        return Pattern::Decreasing;
    }
    Pattern::Poison
}
