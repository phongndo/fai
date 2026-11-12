// The building blocks are HFIR only.
// error: @1:1: agg.make is not allowed in layer mfir; it is allowed in hfir
layer mfir
func @f(%a: i32) {
  %s: i32 = agg.make %a @1:1
  func.ret
}
