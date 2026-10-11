# LLVM MLIR Wavelet Compiler

An experimental Rust compiler that translates a subset of LLVM MLIR into Wavelet source. It lowers SCF into Wavelet functions, infers array capabilities, inserts fences, and adds guards for accesses and calls whose required capabilities cannot be proved available.


## Translation pipeline

1. Parse MLIR with the `memref`, `arith`, `func`, and `scf` dialects loaded.
2. Compute array capabilities and order functions so callees precede callers.
3. Translate operations into Wavelet IR. Lower `scf.for` to recursive helper functions and `scf.if` to conditional tails or helper functions.
4. Type-check the generated IR and rename variables.
5. Insert fences and capability guards using Z3 reasoning.
6. Serialize the program as Wavelet source.

## Supported input

The translator handles a restricted subset of MLIR:

- `func.func`, `func.call`, and `func.return`.
- `scf.for`, `scf.if`, and `scf.yield`, with at most one loop-carried value or conditional result.
- Integer and Boolean constants; integer addition, subtraction, multiplication, signed and unsigned division, comparisons, bitwise operations, and shifts.
- `memref.load` and `memref.store` on statically sized, one-dimensional arrays.
- `memref.distinct_objects` for function array parameters.

Functions with array parameters should begin with `memref.distinct_objects`, as shown in `basic.mlir`, and use the resulting values for accesses. Its optional `alloc_arrays` attribute identifies array results treated as allocated arrays.

`index` and signless/signed integer types map to Wavelet signed integers; unsigned integers map to unsigned integers; `i1` maps to Boolean. Integer widths are not preserved as distinct Wavelet types.