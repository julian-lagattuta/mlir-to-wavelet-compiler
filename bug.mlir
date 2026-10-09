module {
  func.func @write(%i: index, %value: i32, %a0: memref<16xi32>) {
    %a = memref.distinct_objects %a0 : memref<16xi32>
    memref.store %value, %a[%i] : memref<16xi32>
    return
  }
  func.func @wrapper(%i: index, %value: i32, %a0: memref<16xi32>) {
    %a = memref.distinct_objects %a0 : memref<16xi32>
    func.call @write(%i, %value, %a) : (index, i32, memref<16xi32>) -> ()
    return
  }
}
