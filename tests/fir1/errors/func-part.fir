// Function types take value types: in MFIR, scalars.
// error: in @f: @?: struct<C>{i8} can't be a parameter or result of func<(struct<C>{i8})>
layer mfir
func @f(%p: ptr) {
  func.call.indirect func<(struct<C>{i8})> %p()
  func.ret
}
