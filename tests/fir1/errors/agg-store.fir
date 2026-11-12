// Stores take value types.
// error: in @f: @?: operands: expected (struct<C>{i32}, ptr) but got (i32, ptr)
func @f(%p: ptr, %v: i32) {
  mem.store struct<C>{i32} %v, %p, align 4
  func.ret
}
