"module"() ( {
  "llvm.func"() ( {
  ^bb0(%arg0: i32):  // no predecessors
    %0 = "llvm.mlir.constant"() {value = 167772160 : i32} : () -> i32
    %1 = "llvm.mlir.constant"() {value = -16777216 : i32} : () -> i32
    %2 = "llvm.mlir.constant"() {value = 8 : i32} : () -> i32
    %3 = "llvm.shl"(%arg0, %2) : (i32, i32) -> i32
    %4 = "llvm.and"(%3, %1) : (i32, i32) -> i32
    %5 = "llvm.icmp"(%4, %0) {predicate = 0 : i64} : (i32, i32) -> i1
    "llvm.return"(%5) : (i1) -> ()
  }) {linkage = 10 : i64, sym_name = "test", type = !llvm.func<i1 (i32)>} : () -> ()
  "module_terminator"() : () -> ()
}) : () -> ()
