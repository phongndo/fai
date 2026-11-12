// Slices are HFIR only.
// error: @1:1: slice.len is not allowed in layer mfir; it is allowed in hfir
layer mfir
func @f(%p: ptr) {
  %n: i64 = slice.len %p @1:1
  func.ret
}
