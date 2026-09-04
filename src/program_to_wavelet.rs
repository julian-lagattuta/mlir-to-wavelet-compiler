use std::collections::HashSet;

use wavelet_elab::{
    Expr, FnDef, Op, Program, Stmt, Tail, Ty, Val,
    ir::{ArrayLen, Signedness, Variable},
    logic::{cap::CapPattern, region::Region, semantic::solver::Idx},
};

pub fn program_to_wavelet<V: Variable>(program: &Program<V>) -> String {
    let mut output = String::new();

    for (index, definition) in program.defs.iter().enumerate() {
        if index != 0 {
            output.push('\n');
        }
        write_fn(&mut output, definition);
    }

    output
}

fn write_fn<V: Variable>(output: &mut String, definition: &FnDef<V>) {
    if !definition.caps.is_empty() {
        output.push_str("#[cap(");
        let mut first = true;
        for capability in &definition.caps {
            write_capability(
                output,
                capability,
                "uniq",
                capability.uniq.as_ref(),
                &mut first,
            );
            write_capability(
                output,
                capability,
                "shrd",
                capability.shrd.as_ref(),
                &mut first,
            );
        }
        output.push_str(")]\n");
    }

    let const_generics = const_generics(definition);
    output.push_str("fn ");
    output.push_str(&definition.name.0);
    if !const_generics.is_empty() {
        output.push('<');
        for (index, name) in const_generics.iter().enumerate() {
            if index != 0 {
                output.push_str(", ");
            }
            output.push_str("const ");
            output.push_str(name);
            output.push_str(": usize");
        }
        output.push('>');
    }

    output.push('(');
    let mut first = true;
    for parameter in &definition.params {
        if const_generics.contains(&parameter.name) {
            continue;
        }
        if !first {
            output.push_str(", ");
        }
        first = false;
        if definition.alloc_arrays.contains(&parameter.name) {
            output.push_str("#[alloc] ");
        }
        output.push_str(&parameter.name);
        output.push_str(": ");
        write_type(output, &parameter.ty);
    }
    output.push(')');

    if definition.returns != Ty::Unit {
        output.push_str(" -> ");
        write_type(output, &definition.returns);
    }
    output.push_str(" {\n");
    write_expr(output, &definition.body, 1);
    output.push_str("}\n");
}

fn write_capability(
    output: &mut String,
    capability: &CapPattern,
    permission: &str,
    region: Option<&Region>,
    first: &mut bool,
) {
    let Some(region) = region else {
        return;
    };
    if !*first {
        output.push_str(", ");
    }
    *first = false;
    output.push_str(&capability.array);
    output.push_str(": ");
    output.push_str(permission);
    output.push_str(" @ ");
    write_region(output, region);
}

fn write_region(output: &mut String, region: &Region) {
    let intervals: Vec<_> = region.iter().collect();
    if intervals.len() != 1 {
        output.push('{');
    }
    for (index, interval) in intervals.iter().enumerate() {
        if index != 0 {
            output.push_str(", ");
        }
        write_idx(output, &interval.lo);
        output.push_str("..");
        write_idx(output, &interval.hi);
    }
    if intervals.len() != 1 {
        output.push('}');
    }
}

fn write_idx(output: &mut String, index: &Idx) {
    match index {
        Idx::Const(value) if *value < 0 => {
            output.push_str("0 - ");
            output.push_str(&value.unsigned_abs().to_string());
        }
        Idx::Const(value) => output.push_str(&value.to_string()),
        Idx::Var(name) => output.push_str(name),
        Idx::Add(left, right) => {
            write_idx(output, left);
            output.push_str(" + ");
            write_idx(output, right);
        }
        Idx::Sub(left, right) => {
            write_idx(output, left);
            output.push_str(" - ");
            write_idx(output, right);
        }
        Idx::Mul(left, right) => {
            write_idx(output, left);
            output.push_str(" * ");
            write_idx(output, right);
        }
    }
}

fn write_type(output: &mut String, ty: &Ty) {
    match ty {
        Ty::Int(Signedness::Signed) => output.push_str("i32"),
        Ty::Int(Signedness::Unsigned) => output.push_str("usize"),
        Ty::Bool => output.push_str("bool"),
        Ty::Unit => output.push_str("()"),
        Ty::RefShrd { elem, len } => {
            output.push_str("&[");
            write_type(output, elem);
            output.push_str("; ");
            write_array_len(output, len);
            output.push(']');
        }
        Ty::RefUniq { elem, len } => {
            output.push_str("&mut [");
            write_type(output, elem);
            output.push_str("; ");
            write_array_len(output, len);
            output.push(']');
        }
    }
}

fn write_array_len(output: &mut String, len: &ArrayLen) {
    match len {
        ArrayLen::Const(value) => output.push_str(&value.to_string()),
        ArrayLen::Symbol(name) => output.push_str(name),
        ArrayLen::Expr(index) => write_idx_with_parentheses(output, index),
    }
}

fn write_idx_with_parentheses(output: &mut String, index: &Idx) {
    match index {
        Idx::Const(_) | Idx::Var(_) => write_idx(output, index),
        Idx::Add(left, right) => {
            output.push('(');
            write_idx_with_parentheses(output, left);
            output.push_str(" + ");
            write_idx_with_parentheses(output, right);
            output.push(')');
        }
        Idx::Sub(left, right) => {
            output.push('(');
            write_idx_with_parentheses(output, left);
            output.push_str(" - ");
            write_idx_with_parentheses(output, right);
            output.push(')');
        }
        Idx::Mul(left, right) => {
            output.push('(');
            write_idx_with_parentheses(output, left);
            output.push_str(" * ");
            write_idx_with_parentheses(output, right);
            output.push(')');
        }
    }
}

fn write_expr<V: Variable>(output: &mut String, expression: &Expr<V>, depth: usize) {
    for statement in &expression.stmts {
        indent(output, depth);
        write_stmt(output, statement);
        output.push('\n');
        if stmt_is_fenced(statement) {
            indent(output, depth);
            output.push_str("fence!();\n");
        }
    }

    indent(output, depth);
    write_tail(output, &expression.tail, depth);
    output.push('\n');
}

fn write_stmt<V: Variable>(output: &mut String, statement: &Stmt<V>) {
    match statement {
        Stmt::LetVal { var, val, .. } => {
            output.push_str("let ");
            output.push_str(var.name());
            output.push_str(" = ");
            write_val(output, val);
            output.push(';');
        }
        Stmt::LetOp { vars, op, .. } => write_op(output, vars, op),
        Stmt::LetCall {
            vars, func, args, ..
        } => {
            if let Some(var) = vars.first() {
                output.push_str("let ");
                output.push_str(var.name());
                output.push_str(" = ");
            }
            write_call(output, &func.0, args);
            output.push(';');
        }
    }
}

fn write_op<V: Variable>(output: &mut String, vars: &[V], op: &Op<V>) {
    match op {
        Op::Load { array, index, .. } => {
            output.push_str("let ");
            output.push_str(vars[0].name());
            output.push_str(" = ");
            output.push_str(array.name());
            output.push('[');
            output.push_str(index.name());
            output.push_str("];");
        }
        Op::Store {
            array,
            index,
            value,
            ..
        } => {
            output.push_str(array.name());
            output.push('[');
            output.push_str(index.name());
            output.push_str("] = ");
            output.push_str(value.name());
            output.push(';');
        }
        Op::Not => {
            output.push_str("let ");
            output.push_str(vars[1].name());
            output.push_str(" = !");
            output.push_str(vars[0].name());
            output.push(';');
        }
        _ => {
            output.push_str("let ");
            output.push_str(vars[2].name());
            output.push_str(" = ");
            output.push_str(vars[0].name());
            output.push(' ');
            output.push_str(binary_operator(op));
            output.push(' ');
            output.push_str(vars[1].name());
            output.push(';');
        }
    }
}

fn binary_operator<V>(op: &Op<V>) -> &'static str {
    match op {
        Op::Add => "+",
        Op::Sub => "-",
        Op::Mul => "*",
        Op::Sdiv | Op::Udiv => "/",
        Op::And => "&&",
        Op::Or => "||",
        Op::BitAnd => "&",
        Op::BitOr => "|",
        Op::BitXor => "^",
        Op::Shl => "<<",
        Op::Ashr | Op::Lshr => ">>",
        Op::SignedLessThan | Op::UnsignedLessThan => "<",
        Op::SignedLessEqual | Op::UnsignedLessEqual => "<=",
        Op::Equal => "==",
        Op::NotEqual => "!=",
        Op::Not | Op::Load { .. } | Op::Store { .. } => unreachable!(),
    }
}

fn write_tail<V: Variable>(output: &mut String, tail: &Tail<V>, depth: usize) {
    match tail {
        Tail::RetVar(var) => output.push_str(var.name()),
        Tail::TailCall { func, args } => write_call(output, &func.0, args),
        Tail::IfElse {
            cond,
            then_e,
            else_e,
        } => {
            output.push_str("if ");
            output.push_str(cond.name());
            output.push_str(" {\n");
            write_expr(output, then_e, depth + 1);
            indent(output, depth);
            output.push_str("} else {\n");
            write_expr(output, else_e, depth + 1);
            indent(output, depth);
            output.push('}');
        }
    }
}

fn write_call<V: Variable>(output: &mut String, function: &str, args: &[V]) {
    output.push_str(function);
    output.push('(');
    for (index, arg) in args.iter().enumerate() {
        if index != 0 {
            output.push_str(", ");
        }
        output.push_str(arg.name());
    }
    output.push(')');
}

fn write_val(output: &mut String, value: &Val) {
    match value {
        Val::Int(value) => output.push_str(&value.to_string()),
        Val::Bool(value) => output.push_str(if *value { "true" } else { "false" }),
        Val::Unit => output.push_str("()"),
    }
}

fn stmt_is_fenced<V>(statement: &Stmt<V>) -> bool {
    match statement {
        Stmt::LetVal { fence, .. } | Stmt::LetOp { fence, .. } | Stmt::LetCall { fence, .. } => {
            *fence
        }
    }
}

fn const_generics<V>(definition: &FnDef<V>) -> Vec<String> {
    let mut used_in_lengths = HashSet::new();
    for parameter in &definition.params {
        match &parameter.ty {
            Ty::RefShrd { len, .. } | Ty::RefUniq { len, .. } => {
                collect_array_len_vars(len, &mut used_in_lengths)
            }
            _ => {}
        }
    }

    definition
        .params
        .iter()
        .filter(|parameter| {
            parameter.ty == Ty::Int(Signedness::Unsigned)
                && used_in_lengths.contains(&parameter.name)
        })
        .map(|parameter| parameter.name.clone())
        .collect()
}

fn collect_array_len_vars(len: &ArrayLen, variables: &mut HashSet<String>) {
    match len {
        ArrayLen::Const(_) => {}
        ArrayLen::Symbol(name) => {
            variables.insert(name.clone());
        }
        ArrayLen::Expr(index) => collect_idx_vars(index, variables),
    }
}

fn collect_idx_vars(index: &Idx, variables: &mut HashSet<String>) {
    match index {
        Idx::Const(_) => {}
        Idx::Var(name) => {
            variables.insert(name.clone());
        }
        Idx::Add(left, right) | Idx::Sub(left, right) | Idx::Mul(left, right) => {
            collect_idx_vars(left, variables);
            collect_idx_vars(right, variables);
        }
    }
}

fn indent(output: &mut String, depth: usize) {
    for _ in 0..depth {
        output.push_str("    ");
    }
}

#[cfg(test)]
mod tests {
    use wavelet_elab::{
        Expr, FnDef, FnName, Program, Stmt, Tail, Ty, TypedVar, Val, ir::Signedness,
        logic::semantic::solver::Idx, parse_program,
    };

    use super::{program_to_wavelet, write_idx};

    #[test]
    fn negative_index_constants_are_written_as_subtraction_from_zero() {
        let mut serialized = String::new();

        write_idx(&mut serialized, &Idx::Const(-1));

        assert_eq!(serialized, "0 - 1");
    }

    #[test]
    fn serialized_program_can_be_parsed_by_wavelet() {
        let source = r#"
            #[cap(A: uniq @ {i..N, 0..1})]
            fn update<const N: usize>(i: usize, A: &mut [i32; N]) -> i32 {
                let value = A[i];
                fence!();
                A[i] = value;
                if true {
                    update(i, N, A)
                } else {
                    value
                }
            }
        "#;
        let program = parse_program(source).unwrap();
        let serialized = program_to_wavelet(&program);

        parse_program(&serialized).unwrap();
    }

    #[test]
    fn serializes_typed_programs() {
        let int_ty = Ty::Int(Signedness::Signed);
        let program = Program {
            defs: vec![FnDef {
                name: FnName("typed".to_string()),
                params: vec![],
                alloc_arrays: vec![],
                caps: vec![],
                returns: int_ty.clone(),
                body: Expr {
                    stmts: vec![Stmt::LetVal {
                        var: TypedVar::new("value", int_ty.clone()),
                        val: Val::Int(-1),
                        fence: false,
                    }],
                    tail: Tail::RetVar(TypedVar::new("value", int_ty)),
                },
            }],
        };

        let serialized = program_to_wavelet(&program);

        assert_eq!(
            serialized,
            "fn typed() -> i32 {\n    let value = -1;\n    value\n}\n"
        );
        parse_program(&serialized).unwrap();
    }
}
