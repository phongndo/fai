// agg.make takes the fields in order.
// error: @1:1: operands: expected (i32, ptr) but got (ptr, i32)
func @f(%a: i32, %p: ptr) {
  %s: struct<C>{i32, ptr} = agg.make %p, %a @1:1
  func.ret
}
