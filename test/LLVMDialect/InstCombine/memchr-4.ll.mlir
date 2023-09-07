module  {
  llvm.mlir.global external @ax() : !llvm.array<0 x i8>
  llvm.mlir.global external constant @a12345("\01\02\03\04\05")
  llvm.func @memchr(!llvm.ptr<i8>, i32, i64) -> !llvm.ptr<i8>
  llvm.func @call_memchr_ax_2_uimax_p1() -> !llvm.ptr<i8> {
    %0 = llvm.mlir.constant(4294967296 : i64) : i64
    %1 = llvm.mlir.constant(1 : i32) : i32
    %2 = llvm.mlir.constant(0 : i32) : i32
    %3 = llvm.mlir.addressof @ax : !llvm.ptr<array<0 x i8>>
    %4 = llvm.getelementptr %3[%2, %2] : (!llvm.ptr<array<0 x i8>>, i32, i32) -> !llvm.ptr<i8>
    %5 = llvm.call @memchr(%4, %1, %0) : (!llvm.ptr<i8>, i32, i64) -> !llvm.ptr<i8>
    llvm.return %5 : !llvm.ptr<i8>
  }
  llvm.func @call_memchr_ax_2_uimax_p2() -> !llvm.ptr<i8> {
    %0 = llvm.mlir.constant(4294967296 : i64) : i64
    %1 = llvm.mlir.constant(1 : i32) : i32
    %2 = llvm.mlir.constant(0 : i32) : i32
    %3 = llvm.mlir.addressof @ax : !llvm.ptr<array<0 x i8>>
    %4 = llvm.getelementptr %3[%2, %2] : (!llvm.ptr<array<0 x i8>>, i32, i32) -> !llvm.ptr<i8>
    %5 = llvm.call @memchr(%4, %1, %0) : (!llvm.ptr<i8>, i32, i64) -> !llvm.ptr<i8>
    llvm.return %5 : !llvm.ptr<i8>
  }
  llvm.func @fold_memchr_a12345_3_uimax_p2() -> !llvm.ptr<i8> {
    %0 = llvm.mlir.constant(4294967297 : i64) : i64
    %1 = llvm.mlir.constant(3 : i32) : i32
    %2 = llvm.mlir.constant(0 : i32) : i32
    %3 = llvm.mlir.addressof @a12345 : !llvm.ptr<array<5 x i8>>
    %4 = llvm.getelementptr %3[%2, %2] : (!llvm.ptr<array<5 x i8>>, i32, i32) -> !llvm.ptr<i8>
    %5 = llvm.call @memchr(%4, %1, %0) : (!llvm.ptr<i8>, i32, i64) -> !llvm.ptr<i8>
    llvm.return %5 : !llvm.ptr<i8>
  }
  llvm.func @fold_memchr_a12345_c_uimax_p2(%arg0: i32) -> !llvm.ptr<i8> {
    %0 = llvm.mlir.constant(4294967297 : i64) : i64
    %1 = llvm.mlir.constant(0 : i32) : i32
    %2 = llvm.mlir.addressof @a12345 : !llvm.ptr<array<5 x i8>>
    %3 = llvm.getelementptr %2[%1, %1] : (!llvm.ptr<array<5 x i8>>, i32, i32) -> !llvm.ptr<i8>
    %4 = llvm.call @memchr(%3, %arg0, %0) : (!llvm.ptr<i8>, i32, i64) -> !llvm.ptr<i8>
    llvm.return %4 : !llvm.ptr<i8>
  }
}