// LFIR keeps only `func.ret` of the core ops.
// error: in @f: @6:3: int.const is not allowed in layer lfir aarch64; it is allowed in hfir, mfir
layer lfir aarch64

func @f() -> i32 {
  %x: i32 = int.const 1 @6:3
  func.ret %x
}
