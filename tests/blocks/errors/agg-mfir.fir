// MFIR has struct and array values, which calls pass whole, but unions are HFIR only.
// error: @1:1: union.make is not allowed in layer mfir; it is allowed in hfir
layer mfir
func @f(%a: i32) {
  %s: i32 = union.make %a, 0 @1:1
  func.ret
}
