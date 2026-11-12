// MFIR has no slice values.
// error: in @f: @?: slice is not a value type
layer mfir
func @f(%s: slice) {
  func.ret
}
