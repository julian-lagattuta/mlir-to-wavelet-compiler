              module {
                    func.func @read_2d(%array2: memref<100xi32>) {
                        %array = memref.distinct_objects %array2: memref<100xi32>
                        %c0 = arith.constant 0 : index
                        %c1 = arith.constant 1 : index
                        %c10 = arith.constant 10 : index
                        scf.for %i = %c0 to %c10 step %c1 {
                            scf.for %j = %c0 to %c10 step %c1 {
                                %width = arith.constant 10 : index
                                %row = arith.muli %i, %width : index
                                %index = arith.addi %row, %j : index
                                %value = memref.load %array[%index] : memref<100xi32>
                                scf.yield
                            }
                            scf.yield
                        }
                        return
                    }
                }