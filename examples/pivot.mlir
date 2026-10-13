

module {
  func.func @pivot(%a.0: memref<16xi32>) {
    %a = memref.distinct_objects %a.0 : memref<16xi32>

    %c0 = arith.constant 0 : index
    %c1 = arith.constant 1 : index
    %c3 = arith.constant 3 : index
    %c4 = arith.constant 4 : index

    scf.for %k = %c0 to %c3 step %c1 {
      scf.for %j = %c0 to %c4 step %c1 {
        %krow = arith.muli %k, %c4 : index
        %dstrow = arith.addi %krow, %c4 : index
        %src = arith.addi %krow, %j : index
        %dst = arith.addi %dstrow, %j : index
        %value = memref.load %a[%src] : memref<16xi32>
        memref.store %value, %a[%dst] : memref<16xi32>
      }
    }

    func.return
  }
}
