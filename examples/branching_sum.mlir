func.func @sum(%a.0: memref<100xi32>, %b.0: memref<100xi32>)-> i32{
    %a, %b = memref.distinct_objects %a.0, %b.0: memref<100xi32>, memref<100xi32>
    %lb = arith.constant 0 : index 
    %step = arith.constant 1 : index
    %size = arith.constant 100 : index
    %z = arith.constant 0 : i32
    %s = scf.for %iv = %lb to %size step %step iter_args(%v = %z) -> i32{
        %x = memref.load %a[%iv] : memref<100xi32>

        %c = arith.cmpi eq, %x, %z: i32
        %v_next = arith.addi %x, %v : i32
        %o = scf.if %c -> i32{
            %y = memref.load %b[%iv] : memref<100xi32>
            scf.yield %y : i32
        }else{
            scf.yield %v_next : i32
        }
        
        scf.yield %o : i32
    }
    return %s : i32
}