func.func @sum(%a.0: memref<100xi32>)-> i32{
    %a = memref.distinct_objects %a.0: memref<100xi32>
    %lb = arith.constant 0 : index 
    %step = arith.constant 1 : index
    %size = arith.constant 100 : index
    %z = arith.constant 0 : i32
    %s = scf.for %iv = %lb to %size step %step iter_args(%v = %z) -> i32{
        %x = memref.load %a[%iv] : memref<100xi32>
        %v_next = arith.addi %x, %v : i32
        scf.yield %v_next : i32
    }
    return %s : i32
}


