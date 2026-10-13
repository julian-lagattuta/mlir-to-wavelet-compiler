# LLVM MLIR Wavelet Compiler

An experimental Rust compiler that translates a subset of LLVM MLIR into [Wavelet source](https://github.com/plum-umd/wavelet). It lowers SCF into Wavelet functions, infers array capabilities, and inserts fences.
[Wavelet paper](https://lz.gy/papers/wavelet.pdf)

## Wavelet dependency

This project requires the patched Wavelet in `vendor/wavelet`, tracked as a Git submodule from [wavelet-patched](https://github.com/julian-lagattuta/wavelet-patched).

After cloning this repository, initialize the Wavelet checkout:

```sh
cd mlir-to-wavelet-compiler
git submodule update --init vendor/wavelet
```

Cargo uses `vendor/wavelet/wavelet-elab` directly. Run the patched Wavelet compiler from the same checkout:

```sh
cargo run --manifest-path vendor/wavelet/Cargo.toml -- --help
```


## Translation pipeline

1. Parse MLIR with the `memref`, `arith`, `func`, and `scf` dialects loaded.
2. Compute array capabilities and order functions so callees precede callers.
3. Translate operations into Wavelet IR. Lower `scf.for` to recursive helper functions and `scf.if` to conditional tails or helper functions.
4. Type-check the generated IR and rename variables.
5. Insert fences and capability guards using Z3 reasoning.
6. Serialize the program as Wavelet source.

## Supported input 

- `func.func`, `func.call`, `func.return`
  - Cannot return more than one item.
- `scf.if`, `scf.for`, `scf.yield`
  - Cannot yield more than one item.
- `arith`
  - `arith.constant`, `arith.addi`, `arith.subi`, `arith.muli`, `arith.divsi`, `arith.divui`, `arith.cmpi`, `arith.andi`, `arith.ori`, `arith.xori`, `arith.shli`, `arith.shrsi`, `arith.shrui`
- `memref.load`
- `memref.store`
- `memref.distinct_objects`
    - Placed at the beginning of functions to state disjointness of arrays

## Input restrictions

- All `index` values are treated as **signed**.
- Tuples cannot be returned from `scf.if`, `scf.for`, functions, or other constructs. Functions return at most one value, and loops carry at most one `iter_args` value.
- Return statements must be at the top level of the function.
- Function names must be valid Wavelet identifiers. For example, names cannot contain periods.
- `memref` types must be one-dimensional and have a fixed size.
- The first statement of every function with array parameters must declare their disjointness using `memref.distinct_objects`, even if there is only one array. Only the arrays returned by that statement may be accessed.

For example:

```mlir
func.func @f(%a0: memref<16xi32>, %n: index, %b0: memref<16xi32>) {
  %b, %a = memref.distinct_objects %b0, %a0 : memref<16xi32>, memref<16xi32>
  return
}
```

## Limitations

- All integer types are treated as 32-bit integers, regardless of their declared width. `i1` is treated as Boolean.
- Mutual recursion is not supported. Only tail recursion is supported.
- Out-of-bounds accesses may cause the compiler to generate permissions that exceed the array's bounds. The Wavelet ghost checker rejects such programs.

If there is an unknown index, it is forced to fall within the array bounds.

```rust
#[cap(a: uniq @ 0..10)]
fn func(a: &mut [usize; 10]) {
    let z = blackbox();
    a[z] = z;
}
```
becomes
```rust
#[cap(a: uniq @ 0..10)]
fn func(a: &mut [usize; 10]) {
    let z = blackbox();
    let _c0 = z>=0;
    let _c1 = z<10;
    let _c2= _c0 && _c1;
    if _c2{
        a[z] = z;
    }else{
        ()
    }
}
```
