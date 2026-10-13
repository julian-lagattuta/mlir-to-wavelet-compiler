//! Guard accesses that cannot be proved to lie in the function's capability ranges.
//!
//! Wavelet conditionals are tails, so a guard encloses the entire continuation.
//! Its false branch returns a scalar default; its true branch contributes the
//! guard to the assumptions used for every subsequent access.

use std::collections::{HashMap, HashSet};

use anyhow::{Context, Result, bail};
use wavelet_elab::ir::{ArrayLen, Signedness};
use wavelet_elab::logic::{cap::CapPattern, region::Interval, semantic::solver::Idx};
use wavelet_elab::{Expr, FnName, Op, Program, Stmt, Tail, Ty, TypedVar, Val};
use z3::{
    SatResult, Solver,
    ast::{Bool, Int},
};

pub(crate) fn guard_accesses(program: &mut Program<TypedVar>) -> Result<()> {
    let functions: HashMap<_, _> = program
        .defs
        .iter()
        .map(|definition| {
            (
                definition.name.clone(),
                (definition.params.clone(), definition.caps.clone()),
            )
        })
        .collect();
    for definition in &mut program.defs {
        let mut variables = definition
            .params
            .iter()
            .map(|var| (var.name.clone(), var.clone()))
            .collect::<HashMap<_, _>>();
        collect_variables(&definition.body, &mut variables);
        let mut pass = GuardPass {
            solver: Solver::new(),
            functions: &functions,
            caps: &definition.caps,
            names: variables.keys().cloned().collect(),
            variables,
            allocated: &definition.alloc_arrays,
            returns: &definition.returns,
            next_name: 0,
        };
        let mut params = z3::Params::new();
        params.set_u32("timeout", 1000);
        pass.solver.set_params(&params);
        for parameter in &definition.params {
            pass.assume_parameter(parameter);
        }
        definition.body = pass
            .guard_expr(definition.body.clone())
            .with_context(|| format!("failed to guard accesses in {}", definition.name.0))?;
    }
    Ok(())
}

struct GuardPass<'a> {
    solver: Solver,
    functions: &'a HashMap<FnName, (Vec<TypedVar>, Vec<CapPattern>)>,
    caps: &'a [CapPattern],
    variables: HashMap<String, TypedVar>,
    allocated: &'a [String],
    returns: &'a Ty,
    names: HashSet<String>,
    next_name: usize,
}

impl GuardPass<'_> {
    fn fresh(&mut self, ty: Ty) -> TypedVar {
        loop {
            let name = format!("_if_guard_{}", self.next_name);
            self.next_name += 1;
            if self.names.insert(name.clone()) {
                return TypedVar::new(name, ty);
            }
        }
    }

    fn proves(&self, condition: &Bool) -> bool {
        self.solver.push();
        self.solver.assert(condition.not());
        let proved = self.solver.check() == SatResult::Unsat;
        self.solver.pop(1);
        proved
    }

    fn guard_expr(&mut self, expression: Expr<TypedVar>) -> Result<Expr<TypedVar>> {
        let mut statements = Vec::new();
        let mut remaining = expression.stmts.into_iter();
        while let Some(statement) = remaining.next() {
            let guard = if let Stmt::LetOp { op, .. } = &statement {
                let access = match op {
                    Op::Load { array, index, len } => Some((array, index, len, true)),
                    Op::Store {
                        array, index, len, ..
                    } => Some((array, index, len, false)),
                    _ => None,
                };
                if let Some((array, index, len, read)) = access {
                    let intervals = self.intervals(array, len, read);
                    if !self.proves(&membership(&int(index), &intervals)) {
                        Some(self.emit_guard(index, &intervals)?)
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else if let Stmt::LetCall { func, args, .. } = &statement {
                self.call_guard(func, args)?
            } else {
                None
            };
            if let Some((guard_statements, condition)) = guard {
                for guard_statement in &guard_statements {
                    self.assume_statement(guard_statement);
                }
                statements.extend(guard_statements);
                let otherwise = self.default_return()?;
                self.solver.push();
                self.solver.assert(boolean(&condition));
                // The runtime guard protects this access even if a later
                // solver query times out. Do not repeatedly guard it.
                self.assume_statement(&statement);
                let guarded = self
                    .guard_expr(Expr::new(remaining.collect(), expression.tail))
                    .map(|mut continuation| {
                        continuation.stmts.insert(0, statement);
                        continuation
                    });
                self.solver.pop(1);
                return Ok(Expr::new(
                    statements,
                    Tail::IfElse {
                        cond: condition,
                        then_e: Box::new(guarded?),
                        else_e: Box::new(otherwise),
                    },
                ));
            }
            self.assume_statement(&statement);
            statements.push(statement);
        }
        let tail = match expression.tail {
            Tail::IfElse {
                cond,
                then_e,
                else_e,
            } => {
                self.solver.push();
                self.solver.assert(boolean(&cond));
                let then_e = self.guard_expr(*then_e);
                self.solver.pop(1);
                self.solver.push();
                self.solver.assert(boolean(&cond).not());
                let else_e = self.guard_expr(*else_e);
                self.solver.pop(1);
                Tail::IfElse {
                    cond,
                    then_e: Box::new(then_e?),
                    else_e: Box::new(else_e?),
                }
            }
            Tail::TailCall { func, args } => {
                if let Some((guard_statements, condition)) = self.call_guard(&func, &args)? {
                    statements.extend(guard_statements);
                    Tail::IfElse {
                        cond: condition,
                        then_e: Box::new(Expr::new(Vec::new(), Tail::TailCall { func, args })),
                        else_e: Box::new(self.default_return()?),
                    }
                } else {
                    Tail::TailCall { func, args }
                }
            }
            tail => tail,
        };
        Ok(Expr::new(statements, tail))
    }

    fn call_guard(
        &mut self,
        function: &FnName,
        args: &[TypedVar],
    ) -> Result<Option<(Vec<Stmt<TypedVar>>, TypedVar)>> {
        let (parameters, caps) = self
            .functions
            .get(function)
            .with_context(|| format!("unknown function {}", function.0))?;
        if parameters.len() != args.len() {
            bail!("wrong number of arguments to {}", function.0);
        }
        // Match positionally, including array parameters: formal names belong
        // to the callee and must never become unrelated symbols in the caller.
        let substitutions: HashMap<_, _> = parameters
            .iter()
            .zip(args)
            .map(|(parameter, actual)| (parameter.name.clone(), actual.clone()))
            .collect();
        let mut requirements = Vec::new();
        for cap in caps {
            let array = substitutions
                .get(&cap.array)
                .with_context(|| format!("unknown capability array {}", cap.array))?;
            let len = match &array.ty {
                Ty::RefShrd { len, .. } | Ty::RefUniq { len, .. } => len,
                _ => bail!("capability argument {} is not an array", array.name),
            };
            for (region, read) in cap
                .uniq
                .iter()
                .map(|region| (region, false))
                .chain(cap.shrd.iter().map(|region| (region, true)))
            {
                let available = self.intervals(array, len, read);
                for interval in region.iter() {
                    let required = Interval::bounded(
                        substitute_idx(&interval.lo, &substitutions)?,
                        substitute_idx(&interval.hi, &substitutions)?,
                    );
                    if !self.proves(&interval_subset(&required, &available)) {
                        requirements.push((required, available.clone()));
                    }
                }
            }
        }
        let mut statements = Vec::new();
        let mut condition = None;
        for (required, available) in requirements {
            let next = self.emit_subset_guard(&required, &available, &mut statements)?;
            condition = Some(match condition {
                None => next,
                Some(previous) => {
                    self.emit_binary(Op::And, previous, next, Ty::Bool, &mut statements)
                }
            });
        }
        Ok(condition.map(|condition| (statements, condition)))
    }

    fn emit_subset_guard(
        &mut self,
        required: &Interval,
        available: &[Interval],
        statements: &mut Vec<Stmt<TypedVar>>,
    ) -> Result<TypedVar> {
        let ty = idx_variable(&required.lo)
            .or_else(|| idx_variable(&required.hi))
            .or_else(|| {
                available.iter().find_map(|interval| {
                    idx_variable(&interval.lo).or_else(|| idx_variable(&interval.hi))
                })
            })
            .and_then(|name| self.variables.get(name))
            .map(|var| var.ty.clone())
            .unwrap_or(Ty::Int(Signedness::Signed));
        let unsigned = ty == Ty::Int(Signedness::Unsigned);
        let le = if unsigned {
            Op::UnsignedLessEqual
        } else {
            Op::SignedLessEqual
        };
        let start = self.emit_idx(&required.lo, &ty, statements)?;
        let end = self.emit_idx(&required.hi, &ty, statements)?;
        let empty = self.emit_binary(le.clone(), end.clone(), start.clone(), Ty::Bool, statements);
        if available.is_empty() {
            return Ok(empty);
        }
        if let [interval] = available {
            let lo = self.emit_idx(&interval.lo, &ty, statements)?;
            let hi = self.emit_idx(&interval.hi, &ty, statements)?;
            let lower = self.emit_binary(le.clone(), lo, start, Ty::Bool, statements);
            let upper = self.emit_binary(le, end, hi, Ty::Bool, statements);
            let inside = self.emit_binary(Op::And, lower, upper, Ty::Bool, statements);
            return Ok(self.emit_binary(Op::Or, empty, inside, Ty::Bool, statements));
        }
        let (initial, mut covered) = self.emit_guard(&start, available)?;
        statements.extend(initial);
        // A gap within a finite union starts at one of its upper endpoints.
        // Cover the start and every endpoint strictly inside the requested range.
        // This permits spans across adjacent/overlapping intervals, but not holes.
        for interval in available {
            let hi = self.emit_idx(&interval.hi, &ty, statements)?;
            let before =
                self.emit_binary(le.clone(), hi.clone(), start.clone(), Ty::Bool, statements);
            let after = self.emit_binary(le.clone(), end.clone(), hi.clone(), Ty::Bool, statements);
            let outside = self.emit_binary(Op::Or, before, after, Ty::Bool, statements);
            let (endpoint_statements, endpoint_covered) = self.emit_guard(&hi, available)?;
            statements.extend(endpoint_statements);
            let no_gap = self.emit_binary(Op::Or, outside, endpoint_covered, Ty::Bool, statements);
            covered = self.emit_binary(Op::And, covered, no_gap, Ty::Bool, statements);
        }
        Ok(self.emit_binary(Op::Or, empty, covered, Ty::Bool, statements))
    }

    fn intervals(&self, array: &TypedVar, len: &ArrayLen, read: bool) -> Vec<Interval> {
        let mut intervals = Vec::new();
        for cap in self.caps.iter().filter(|cap| cap.array == array.name) {
            for region in cap.uniq.iter().chain(cap.shrd.iter().filter(|_| read)) {
                intervals.extend(region.iter().cloned());
            }
        }
        if self.allocated.contains(&array.name) {
            let hi = match len {
                ArrayLen::Const(n) => Idx::Const(*n as i64),
                ArrayLen::Symbol(name) => Idx::Var(name.clone()),
                ArrayLen::Expr(index) => index.clone(),
            };
            intervals.push(Interval::bounded(Idx::Const(0), hi));
        }
        intervals
    }

    fn emit_guard(
        &mut self,
        index: &TypedVar,
        intervals: &[Interval],
    ) -> Result<(Vec<Stmt<TypedVar>>, TypedVar)> {
        let mut statements = Vec::new();
        let mut membership = None;
        let unsigned = index.ty == Ty::Int(Signedness::Unsigned);
        for interval in intervals {
            let lo = self.emit_idx(&interval.lo, &index.ty, &mut statements)?;
            let hi = self.emit_idx(&interval.hi, &index.ty, &mut statements)?;
            let lower = self.emit_binary(
                if unsigned {
                    Op::UnsignedLessEqual
                } else {
                    Op::SignedLessEqual
                },
                lo,
                index.clone(),
                Ty::Bool,
                &mut statements,
            );
            let upper = self.emit_binary(
                if unsigned {
                    Op::UnsignedLessThan
                } else {
                    Op::SignedLessThan
                },
                index.clone(),
                hi,
                Ty::Bool,
                &mut statements,
            );
            let inside = self.emit_binary(Op::And, lower, upper, Ty::Bool, &mut statements);
            membership = Some(match membership {
                None => inside,
                Some(previous) => {
                    self.emit_binary(Op::Or, previous, inside, Ty::Bool, &mut statements)
                }
            });
        }
        let condition = membership
            .unwrap_or_else(|| self.emit_value(Val::Bool(false), Ty::Bool, &mut statements));
        Ok((statements, condition))
    }

    fn emit_idx(
        &mut self,
        index: &Idx,
        ty: &Ty,
        statements: &mut Vec<Stmt<TypedVar>>,
    ) -> Result<TypedVar> {
        Ok(match index {
            Idx::Const(n) => self.emit_value(Val::Int(*n), ty.clone(), statements),
            Idx::Var(name) => {
                let Some(variable) = self.variables.get(name) else {
                    bail!("capability bound '{name}' is not in scope");
                };
                if &variable.ty != ty {
                    bail!(
                        "capability bound '{name}' and access index have different integer types"
                    );
                }
                variable.clone()
            }
            Idx::Add(lhs, rhs) | Idx::Sub(lhs, rhs) | Idx::Mul(lhs, rhs) => {
                let lhs = self.emit_idx(lhs, ty, statements)?;
                let rhs = self.emit_idx(rhs, ty, statements)?;
                let op = match index {
                    Idx::Add(..) => Op::Add,
                    Idx::Sub(..) => Op::Sub,
                    _ => Op::Mul,
                };
                self.emit_binary(op, lhs, rhs, ty.clone(), statements)
            }
        })
    }

    fn emit_value(&mut self, val: Val, ty: Ty, statements: &mut Vec<Stmt<TypedVar>>) -> TypedVar {
        let var = self.fresh(ty);
        statements.push(Stmt::LetVal {
            var: var.clone(),
            val,
            fence: false,
        });
        var
    }

    fn emit_binary(
        &mut self,
        op: Op<TypedVar>,
        lhs: TypedVar,
        rhs: TypedVar,
        ty: Ty,
        statements: &mut Vec<Stmt<TypedVar>>,
    ) -> TypedVar {
        let result = self.fresh(ty);
        statements.push(Stmt::LetOp {
            vars: vec![lhs, rhs, result.clone()],
            op,
            fence: false,
        });
        result
    }

    fn default_return(&mut self) -> Result<Expr<TypedVar>> {
        let value = match self.returns {
            Ty::Unit => Val::Unit,
            Ty::Int(_) => Val::Int(0),
            Ty::Bool => Val::Bool(false),
            _ => bail!("cannot supply a default return value for an array reference"),
        };
        let mut statements = Vec::new();
        let result = self.emit_value(value, self.returns.clone(), &mut statements);
        Ok(Expr::new(statements, Tail::RetVar(result)))
    }

    fn assume_parameter(&self, var: &TypedVar) {
        // Only parameters receive unsigned domain assumptions. Locals may be
        // negative regardless of the signedness attached by type inference.
        if var.ty == Ty::Int(Signedness::Unsigned) {
            self.solver.assert(int(var).ge(0));
        }
    }

    fn assume_statement(&self, statement: &Stmt<TypedVar>) {
        match statement {
            Stmt::LetVal { var, val, .. } => match val {
                Val::Int(n) => self.solver.assert(int(var).eq(Int::from_i64(*n))),
                Val::Bool(b) => self.solver.assert(boolean(var).eq(Bool::from_bool(*b))),
                Val::Unit => {}
            },
            // Calls (including blackbox) and loads produce unconstrained values.
            // Local integers are signed in Z3 even when their IR type is unsigned.
            Stmt::LetCall { .. } => {}
            Stmt::LetOp { vars, op, .. } => {
                if let Op::Not = op {
                    self.solver
                        .assert(boolean(&vars[1]).eq(boolean(&vars[0]).not()));
                } else if vars.len() == 3 {
                    let (lhs, rhs, result) = (&vars[0], &vars[1], &vars[2]);
                    // Use the same mathematical Int model as capability/fence analysis.
                    let numeric = match op {
                        Op::Add => Some(int(lhs) + int(rhs)),
                        Op::Sub => Some(int(lhs) - int(rhs)),
                        Op::Mul => Some(int(lhs) * int(rhs)),
                        _ => None,
                    };
                    if let Some(value) = numeric {
                        self.solver.assert(int(result).eq(value));
                        return;
                    }
                    let condition = match op {
                        Op::And => Some(Bool::and(&[boolean(lhs), boolean(rhs)])),
                        Op::Or => Some(Bool::or(&[boolean(lhs), boolean(rhs)])),
                        Op::SignedLessThan | Op::UnsignedLessThan => Some(int(lhs).lt(int(rhs))),
                        Op::SignedLessEqual | Op::UnsignedLessEqual => Some(int(lhs).le(int(rhs))),
                        Op::Equal | Op::NotEqual if lhs.ty == Ty::Bool || lhs.ty.is_int() => {
                            let equal = if lhs.ty == Ty::Bool {
                                boolean(lhs).eq(boolean(rhs))
                            } else {
                                int(lhs).eq(int(rhs))
                            };
                            Some(if matches!(op, Op::NotEqual) {
                                equal.not()
                            } else {
                                equal
                            })
                        }
                        _ => None,
                    };
                    if let Some(condition) = condition {
                        self.solver.assert(boolean(result).eq(condition));
                    }
                    // Unsupported operations remain unconstrained; they cannot prove safety.
                }
            }
        }
    }
}

fn int(var: &TypedVar) -> Int {
    Int::new_const(var.name.clone())
}
fn boolean(var: &TypedVar) -> Bool {
    Bool::new_const(var.name.clone())
}

fn idx_to_z3(index: &Idx) -> Int {
    match index {
        Idx::Const(n) => Int::from_i64(*n),
        Idx::Var(name) => Int::new_const(name.clone()),
        Idx::Add(lhs, rhs) => idx_to_z3(lhs) + idx_to_z3(rhs),
        Idx::Sub(lhs, rhs) => idx_to_z3(lhs) - idx_to_z3(rhs),
        Idx::Mul(lhs, rhs) => idx_to_z3(lhs) * idx_to_z3(rhs),
    }
}

fn membership(index: &Int, intervals: &[Interval]) -> Bool {
    Bool::or(
        &intervals
            .iter()
            .map(|interval| {
                Bool::and(&[
                    index.ge(idx_to_z3(&interval.lo)),
                    index.lt(idx_to_z3(&interval.hi)),
                ])
            })
            .collect::<Vec<_>>(),
    )
}

fn interval_subset(required: &Interval, available: &[Interval]) -> Bool {
    let start = idx_to_z3(&required.lo);
    let end = idx_to_z3(&required.hi);
    let covered = if let [interval] = available {
        Bool::and(&[
            start.ge(idx_to_z3(&interval.lo)),
            end.le(idx_to_z3(&interval.hi)),
        ])
    } else {
        let mut conditions = vec![membership(&start, available)];
        for interval in available {
            let hi = idx_to_z3(&interval.hi);
            conditions.push(Bool::or(&[
                hi.le(&start),
                end.le(&hi),
                membership(&hi, available),
            ]));
        }
        Bool::and(&conditions)
    };
    Bool::or(&[end.le(&start), covered])
}

fn substitute_idx(index: &Idx, substitutions: &HashMap<String, TypedVar>) -> Result<Idx> {
    Ok(match index {
        Idx::Const(n) => Idx::Const(*n),
        Idx::Var(name) => Idx::Var(
            substitutions
                .get(name)
                .with_context(|| format!("unknown capability parameter {name}"))?
                .name
                .clone(),
        ),
        Idx::Add(lhs, rhs) => Idx::Add(
            Box::new(substitute_idx(lhs, substitutions)?),
            Box::new(substitute_idx(rhs, substitutions)?),
        ),
        Idx::Sub(lhs, rhs) => Idx::Sub(
            Box::new(substitute_idx(lhs, substitutions)?),
            Box::new(substitute_idx(rhs, substitutions)?),
        ),
        Idx::Mul(lhs, rhs) => Idx::Mul(
            Box::new(substitute_idx(lhs, substitutions)?),
            Box::new(substitute_idx(rhs, substitutions)?),
        ),
    })
}

fn idx_variable(index: &Idx) -> Option<&str> {
    match index {
        Idx::Var(name) => Some(name),
        Idx::Add(lhs, rhs) | Idx::Sub(lhs, rhs) | Idx::Mul(lhs, rhs) => {
            idx_variable(lhs).or_else(|| idx_variable(rhs))
        }
        Idx::Const(_) => None,
    }
}

fn collect_variables(expression: &Expr<TypedVar>, variables: &mut HashMap<String, TypedVar>) {
    for statement in &expression.stmts {
        match statement {
            Stmt::LetVal { var, .. } => {
                variables.insert(var.name.clone(), var.clone());
            }
            Stmt::LetOp { vars, .. } | Stmt::LetCall { vars, .. } => {
                variables.extend(vars.iter().map(|var| (var.name.clone(), var.clone())));
            }
        }
    }
    if let Tail::IfElse { then_e, else_e, .. } = &expression.tail {
        collect_variables(then_e, variables);
        collect_variables(else_e, variables);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program_to_wavelet::program_to_wavelet;
    use wavelet_elab::{infer_program, parse_program};

    fn run(source: &str) -> Program<TypedVar> {
        let mut program = infer_program(&parse_program(source).unwrap()).unwrap();
        guard_accesses(&mut program).unwrap();
        // Verify the emitted source is accepted and still has consistent types.
        infer_program(&parse_program(&program_to_wavelet(&program)).unwrap()).unwrap();
        program
    }

    fn guards(expression: &Expr<TypedVar>) -> usize {
        match &expression.tail {
            Tail::IfElse {
                cond,
                then_e,
                else_e,
            } => usize::from(cond.name.starts_with("_if_guard_")) + guards(then_e) + guards(else_e),
            _ => 0,
        }
    }

    #[test]
    fn safe_arithmetic_is_unchanged() {
        let source = "#[cap(A: uniq @ 0..8)] fn write(A: &mut [i32; 8]) { let i = 2 + 3; let value = 1; A[i] = value; () }";
        let original = infer_program(&parse_program(source).unwrap()).unwrap();
        let mut program = original.clone();
        guard_accesses(&mut program).unwrap();
        assert_eq!(program, original);
    }

    #[test]
    fn union_preserves_holes_and_half_open_bounds() {
        for (index, needs_guard) in [
            (-1, true),
            (0, false),
            (1, false),
            (2, true),
            (3, true),
            (4, false),
            (7, false),
            (8, true),
        ] {
            let source = format!(
                "#[cap(A: uniq @ {{0..2, 4..8}})] fn write(A: &mut [i32; 8]) {{ let i = {index}; let value = 1; A[i] = value; () }}"
            );
            assert_eq!(
                guards(&run(&source).defs[0].body),
                usize::from(needs_guard),
                "index {index}"
            );
        }
    }

    #[test]
    fn emitted_guard_tests_the_union_instead_of_its_bounding_interval() {
        let program = run(
            "#[cap(A: uniq @ {0..2, 4..8})] fn write(i: i32, A: &mut [i32; 8]) { let value = 1; A[i] = value; () }",
        );
        let body = &program.defs[0].body;
        let Tail::IfElse { cond, .. } = &body.tail else {
            panic!("missing guard")
        };
        // Evaluate the emitted pure statements independently of Z3.
        for (index, expected) in [
            (-1, false),
            (0, true),
            (1, true),
            (2, false),
            (3, false),
            (4, true),
            (7, true),
            (8, false),
        ] {
            let mut values = HashMap::from([("i".to_string(), Val::Int(index))]);
            for statement in &body.stmts {
                match statement {
                    Stmt::LetVal { var, val, .. } => {
                        values.insert(var.name.clone(), val.clone());
                    }
                    Stmt::LetOp { vars, op, .. } => {
                        let lhs = &values[&vars[0].name];
                        let rhs = &values[&vars[1].name];
                        let value = match (op, lhs, rhs) {
                            (Op::SignedLessThan, Val::Int(a), Val::Int(b)) => a < b,
                            (Op::SignedLessEqual, Val::Int(a), Val::Int(b)) => a <= b,
                            (Op::And, Val::Bool(a), Val::Bool(b)) => *a && *b,
                            (Op::Or, Val::Bool(a), Val::Bool(b)) => *a || *b,
                            _ => panic!("unexpected guard operation"),
                        };
                        values.insert(vars[2].name.clone(), Val::Bool(value));
                    }
                    _ => panic!("unexpected guard statement"),
                }
            }
            assert_eq!(values[&cond.name], Val::Bool(expected), "index {index}");
        }
    }

    #[test]
    fn guard_assumption_protects_later_accesses_and_keeps_fences() {
        let program = run(
            "#[cap(A: uniq @ 0..8)] fn write(i: i32, A: &mut [i32; 8]) { let value = 1; A[i] = value; fence!(); let j = i + 0; A[j] = value; () }",
        );
        let body = &program.defs[0].body;
        assert_eq!(guards(body), 1);
        let Tail::IfElse { then_e, else_e, .. } = &body.tail else {
            panic!("missing guard")
        };
        assert!(then_e.stmts.iter().any(|stmt| matches!(
            stmt,
            Stmt::LetOp {
                op: Op::Store { .. },
                fence: true,
                ..
            }
        )));
        assert!(matches!(
            &else_e.stmts[0],
            Stmt::LetVal { val: Val::Unit, .. }
        ));
    }

    #[test]
    fn unrelated_unknown_indices_need_separate_guards() {
        let program = run(
            "fn blackbox() -> i32 { 5 } #[cap(A: uniq @ 0..8)] fn write(A: &mut [i32; 8]) { let value = 1; let i = blackbox(); A[i] = value; let j = blackbox(); A[j] = value; () }",
        );
        assert_eq!(guards(&program.defs[1].body), 2);
    }

    #[test]
    fn existing_if_assumptions_are_scoped_to_each_branch() {
        let program = run(
            "#[cap(A: uniq @ 0..8)] fn write(i: i32, A: &mut [i32; 8]) { let value = 1; let lower = 0 <= i; let upper = i < 8; let safe = lower && upper; if safe { A[i] = value; () } else { A[i] = value; () } }",
        );
        let Tail::IfElse { then_e, else_e, .. } = &program.defs[0].body.tail else {
            panic!("missing original if")
        };
        assert_eq!(guards(then_e), 0);
        assert_eq!(guards(else_e), 1);

        let program = run(
            "#[cap(A: uniq @ 0..8)] fn write(i: i32, A: &mut [i32; 8]) { let value = 1; let lower = i < 0; let upper = 8 <= i; let unsafe_index = lower || upper; if unsafe_index { A[i] = value; () } else { A[i] = value; () } }",
        );
        let Tail::IfElse { then_e, else_e, .. } = &program.defs[0].body.tail else {
            panic!("missing original if")
        };
        assert_eq!(guards(then_e), 1);
        assert_eq!(guards(else_e), 0);
    }

    #[test]
    fn negated_if_and_boolean_equality_are_assumptions() {
        let program = run(
            "#[cap(A: uniq @ 0..8)] fn read(i: i32, A: &mut [i32; 8]) -> i32 { let lower = 0 <= i; let upper = i < 8; let safe = lower && upper; let unsafe_index = !safe; let condition = unsafe_index == false; if condition { let value = A[i]; value } else { 0 } }",
        );
        assert_eq!(guards(&program.defs[0].body), 0);
    }

    #[test]
    fn loads_use_shared_and_unique_ranges_but_stores_require_unique() {
        let program = run(
            "#[cap(A: shrd @ 0..4, A: uniq @ 4..8)] fn read(A: &mut [i32; 8]) -> i32 { let i = 1; let j = 5; let x = A[i]; let y = A[j]; let sum = x + y; sum }",
        );
        assert_eq!(guards(&program.defs[0].body), 0);
        let program = run(
            "#[cap(A: shrd @ 0..4, A: uniq @ 4..8)] fn write(A: &mut [i32; 8]) { let i = 1; let value = 1; A[i] = value; () }",
        );
        assert_eq!(guards(&program.defs[0].body), 1);
    }

    #[test]
    fn absent_or_empty_capabilities_do_not_allow_accesses() {
        for annotation in ["", "#[cap(A: uniq @ {})]"] {
            let source = format!(
                "{annotation} fn write(A: &mut [i32; 8]) {{ let i = 0; let value = 1; A[i] = value; () }}"
            );
            let program = run(&source);
            assert_eq!(guards(&program.defs[0].body), 1);
            assert!(program.defs[0].body.stmts.iter().any(|stmt| matches!(
                stmt,
                Stmt::LetVal {
                    val: Val::Bool(false),
                    ..
                }
            )));
        }
    }

    #[test]
    fn failed_loads_return_scalar_defaults() {
        for (elem, default) in [("i32", Val::Int(0)), ("bool", Val::Bool(false))] {
            let source = format!(
                "#[cap(A: shrd @ 0..8)] fn read(i: i32, A: &[{elem}; 8]) -> {elem} {{ let value = A[i]; value }}"
            );
            let program = run(&source);
            let Tail::IfElse { else_e, .. } = &program.defs[0].body.tail else {
                panic!("missing guard")
            };
            assert!(matches!(&else_e.stmts[0], Stmt::LetVal { val, .. } if *val == default));
        }
    }

    #[test]
    fn symbolic_union_bounds_are_emitted_and_typed() {
        let program = run(
            "#[cap(A: uniq @ {lo..lo + 2, 6..8})] fn write(lo: i32, i: i32, A: &mut [i32; 8]) { let value = 1; A[i] = value; A[i] = value; () }",
        );
        assert_eq!(guards(&program.defs[0].body), 1);
        assert!(
            program.defs[0]
                .body
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, Stmt::LetOp { op: Op::Or, .. }))
        );
    }

    #[test]
    fn unsigned_domain_and_guard_types_are_preserved() {
        let program = run(
            "#[cap(A: uniq @ 0..8)] fn write(i: usize, A: &mut [i32; 8]) { let value = 1; A[i] = value; () }",
        );
        assert_eq!(guards(&program.defs[0].body), 1);
        assert!(program.defs[0].body.stmts.iter().any(|stmt| matches!(
            stmt,
            Stmt::LetOp {
                op: Op::UnsignedLessThan,
                ..
            }
        )));
    }

    #[test]
    fn only_unsigned_parameters_have_nonnegative_assumptions() {
        let program = run(
            "#[cap(A: uniq @ 0..8)] fn write(i: usize, A: &mut [i32; 8]) { let value = 1; let upper = i < 8; if upper { A[i] = value; () } else { () } }",
        );
        assert_eq!(guards(&program.defs[0].body), 0);

        let program = run(
            "fn blackbox() -> usize { 5 } #[cap(A: uniq @ 0..8)] fn write(A: &mut [i32; 8]) { let value = 1; let i = blackbox(); let upper = i < 8; if upper { A[i] = value; () } else { () } }",
        );
        assert_eq!(guards(&program.defs[1].body), 1);

        let program = run(
            "#[cap(A: uniq @ 0..8)] fn write(i: usize, A: &mut [i32; 8]) { let value = 1; let j = i - 1; let upper = j < 8; if upper { A[j] = value; () } else { () } }",
        );
        assert_eq!(guards(&program.defs[0].body), 1);

        let program = run(
            "#[cap(B: shrd @ 0..1, A: uniq @ 0..8)] fn write(B: &[usize; 1], A: &mut [i32; 8]) { let value = 1; let zero = 0; let i = B[zero]; let upper = i < 8; if upper { A[i] = value; () } else { () } }",
        );
        assert_eq!(guards(&program.defs[0].body), 1);
    }

    #[test]
    fn generated_names_do_not_collide_and_pass_is_idempotent() {
        let mut program = run(
            "#[cap(A: uniq @ 0..8)] fn write(_if_guard_0: i32, A: &mut [i32; 8]) { let value = 1; A[_if_guard_0] = value; () }",
        );
        assert!(
            !program.defs[0]
                .body
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, Stmt::LetVal { var, .. } if var.name == "_if_guard_0"))
        );
        let once = program.clone();
        guard_accesses(&mut program).unwrap();
        assert_eq!(program, once);
    }

    #[test]
    fn unsupported_index_operations_remain_unknown() {
        let program = run(
            "#[cap(A: uniq @ 0..8)] fn write(i: i32, A: &mut [i32; 8]) { let value = 1; let j = i / 2; A[j] = value; () }",
        );
        assert_eq!(guards(&program.defs[0].body), 1);
    }

    #[test]
    fn call_guard_substitutes_local_indices_and_guards_later_accesses() {
        let program = run(r#"
            fn blackbox() -> i32 { 5 }
            #[cap(A: uniq @ n..n + 1)]
            fn write(n: i32, A: &mut [i32; 8]) {
                let value = 1;
                A[n] = value;
                ()
            }
            #[cap(B: uniq @ 0..8)]
            fn caller(B: &mut [i32; 8]) {
                let i = blackbox();
                let result = write(i, B);
                fence!();
                let value = 2;
                B[i] = value;
                ()
            }
        "#);
        assert_eq!(guards(&program.defs[2].body), 1);
        let Tail::IfElse { then_e, .. } = &program.defs[2].body.tail else {
            panic!("missing call guard")
        };
        assert!(then_e.stmts.iter().any(|statement| matches!(statement, Stmt::LetCall { func, fence: true, .. } if func.0 == "write")));
        check_normal(&program);
    }

    #[test]
    fn tail_calls_are_guarded_and_the_pass_remains_idempotent() {
        let mut program = run(r#"
            #[cap(A: uniq @ n..n + 1)]
            fn write(n: i32, A: &mut [i32; 8]) {
                let value = 1;
                A[n] = value;
                ()
            }
            #[cap(B: uniq @ 0..8)]
            fn caller(i: i32, B: &mut [i32; 8]) { write(i, B) }
        "#);
        assert_eq!(guards(&program.defs[1].body), 1);
        let once = program.clone();
        guard_accesses(&mut program).unwrap();
        assert_eq!(program, once);
        check_normal(&program);
    }

    #[test]
    fn call_substitution_is_simultaneous_for_reordered_arrays_and_scalars() {
        let program = run(r#"
            #[cap(A: uniq @ n..n + 1, B: shrd @ k..k + 1)]
            fn copy(n: i32, k: i32, A: &mut [i32; 8], B: &mut [i32; 8]) {
                let value = B[k];
                A[n] = value;
                ()
            }
            #[cap(P: shrd @ 4..8, Q: uniq @ 0..4)]
            fn caller(P: &mut [i32; 8], Q: &mut [i32; 8]) {
                let n = 6;
                let k = 2;
                copy(k, n, Q, P)
            }
        "#);
        assert_eq!(guards(&program.defs[1].body), 0);
        check_normal(&program);
    }

    #[test]
    fn a_call_guard_checks_all_arrays_and_permission_kinds() {
        let program = run(r#"
            #[cap(A: uniq @ n..n + 1, B: shrd @ k..k + 1)]
            fn copy(n: i32, k: i32, A: &mut [i32; 8], B: &mut [i32; 8]) {
                let value = B[k];
                A[n] = value;
                ()
            }
            #[cap(P: shrd @ 4..8, Q: uniq @ 0..4)]
            fn caller(i: i32, j: i32, P: &mut [i32; 8], Q: &mut [i32; 8]) {
                copy(i, j, Q, P)
            }
        "#);
        assert_eq!(guards(&program.defs[1].body), 1);
        let body = &program.defs[1].body;
        for (i, j, expected) in [(2, 6, true), (4, 6, false), (2, 3, false), (-1, 6, false)] {
            assert_eq!(evaluate_guard(body, [("i", i), ("j", j)]), expected);
        }
        check_normal(&program);
    }

    #[test]
    fn call_range_guards_cover_adjacent_unions_and_preserve_gaps() {
        for (ranges, samples) in [
            (
                "{0..2, 2..8}",
                vec![
                    (-1, true),
                    (0, true),
                    (1, true),
                    (2, true),
                    (3, true),
                    (8, true),
                    (9, false),
                ],
            ),
            (
                "{0..2, 4..8}",
                vec![
                    (0, true),
                    (1, true),
                    (2, true),
                    (3, false),
                    (4, false),
                    (8, false),
                ],
            ),
        ] {
            let program = run(&format!(
                r#"
                #[cap(A: uniq @ lo..hi)]
                fn span(lo: i32, hi: i32, A: &mut [i32; 8]) {{ () }}
                #[cap(B: uniq @ {ranges})]
                fn caller(end: i32, B: &mut [i32; 8]) {{
                    let zero = 0;
                    span(zero, end, B)
                }}
            "#
            ));
            assert_eq!(guards(&program.defs[1].body), 1);
            for (end, expected) in samples {
                assert_eq!(
                    evaluate_guard(&program.defs[1].body, [("end", end)]),
                    expected,
                    "{ranges}, end={end}"
                );
            }
            check_normal(&program);
        }
    }

    #[test]
    fn call_range_checks_do_not_guard_already_proven_spans() {
        let source = r#"
            #[cap(A: uniq @ lo..hi)]
            fn span(lo: i32, hi: i32, A: &mut [i32; 8]) { () }
            #[cap(B: uniq @ {0..2, 2..8})]
            fn caller(B: &mut [i32; 8]) {
                let lo = 0;
                let hi = 8;
                span(lo, hi, B)
            }
        "#;
        let mut program = infer_program(&parse_program(source).unwrap()).unwrap();
        let original = program.clone();
        guard_accesses(&mut program).unwrap();
        assert_eq!(program, original);
        check_normal(&program);
    }

    #[test]
    fn call_writes_cannot_use_shared_permissions() {
        let program = run(r#"
            #[cap(A: uniq @ n..n + 1)]
            fn write(n: i32, A: &mut [i32; 8]) { () }
            #[cap(B: shrd @ 0..8)]
            fn caller(i: i32, B: &mut [i32; 8]) { write(i, B) }
        "#);
        assert_eq!(guards(&program.defs[1].body), 1);
        for i in [0, 3, 7] {
            assert!(!evaluate_guard(&program.defs[1].body, [("i", i)]));
        }
        check_normal(&program);
    }

    fn check_normal(program: &Program<TypedVar>) {
        use wavelet_elab::logic::semantic::solver::{SmtBackend, SmtSolver};
        let logic =
            wavelet_elab::SemanticLogic::with_solver(SmtSolver::with_backend(SmtBackend::Z3));
        let source = program_to_wavelet(program);
        wavelet_elab::check_program(&parse_program(&source).unwrap(), &logic).unwrap();
    }

    fn evaluate_guard<const N: usize>(
        expression: &Expr<TypedVar>,
        inputs: [(&str, i64); N],
    ) -> bool {
        let mut values: HashMap<_, _> = inputs
            .into_iter()
            .map(|(name, value)| (name.to_string(), Val::Int(value)))
            .collect();
        for statement in &expression.stmts {
            match statement {
                Stmt::LetVal { var, val, .. } => {
                    values.insert(var.name.clone(), val.clone());
                }
                Stmt::LetOp { vars, op, .. } => {
                    let lhs = &values[&vars[0].name];
                    let rhs = &values[&vars[1].name];
                    let value = match (op, lhs, rhs) {
                        (Op::Add, Val::Int(a), Val::Int(b)) => Val::Int(a + b),
                        (Op::Sub, Val::Int(a), Val::Int(b)) => Val::Int(a - b),
                        (Op::Mul, Val::Int(a), Val::Int(b)) => Val::Int(a * b),
                        (Op::SignedLessThan | Op::UnsignedLessThan, Val::Int(a), Val::Int(b)) => {
                            Val::Bool(a < b)
                        }
                        (Op::SignedLessEqual | Op::UnsignedLessEqual, Val::Int(a), Val::Int(b)) => {
                            Val::Bool(a <= b)
                        }
                        (Op::And, Val::Bool(a), Val::Bool(b)) => Val::Bool(*a && *b),
                        (Op::Or, Val::Bool(a), Val::Bool(b)) => Val::Bool(*a || *b),
                        _ => panic!("unexpected guard operation"),
                    };
                    values.insert(vars[2].name.clone(), value);
                }
                _ => panic!("unexpected guard statement"),
            }
        }
        let Tail::IfElse { cond, .. } = &expression.tail else {
            panic!("missing guard")
        };
        let Val::Bool(result) = values[&cond.name] else {
            panic!("non-boolean guard")
        };
        result
    }
}
