// Function types take value types.
// error: in @f: @?: struct<C>{i8} can't be a parameter or result of func<(struct<C>{i8})>
func @f(%p: ptr) {
  func.call.indirect func<(struct<C>{i8})> %p()
  func.ret
}
