// Function types take value types: in MFIR, scalars and composites, not slices.
// error: in @f: @?: slice can't be a parameter or result of func<(slice)>
layer mfir
func @f(%p: ptr) {
  func.call.indirect func<(slice)> %p()
  func.ret
}
