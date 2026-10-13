func.func @trailing_reads(%a.0: memref<100xi32>) -> i32 {
    %a = memref.distinct_objects %a.0 : memref<100xi32>
    %lb = arith.constant 0 : index
    %step = arith.constant 1 : index
    %size = arith.constant 100 : index
    %z = arith.constant 0 : i32
    %s = scf.for %iv = %lb to %size step %step iter_args(%v = %z) -> i32 {
        memref.store %v, %a[%iv] : memref<100xi32>
        %has_trailing = arith.cmpi sgt, %iv, %lb : index
        %v_next = scf.if %has_trailing -> i32 {
            %trailing = arith.subi %iv, %step : index
            %x = memref.load %a[%trailing] : memref<100xi32>
            %sum = arith.addi %x, %v : i32
            scf.yield %sum : i32
        } else {
            scf.yield %v : i32
        }
        scf.yield %v_next : i32
    }
    return %s : i32
}
