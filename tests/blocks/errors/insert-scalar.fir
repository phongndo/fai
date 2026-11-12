// agg.insert takes a struct or an array.
// error: @1:1: ptr is not a struct or an array
func @f(%p: ptr) {
  %t: ptr = agg.insert %p, %p, 0 @1:1
  func.ret
}
