// agg.make makes structs and arrays.
// error: @1:1: i32 is not a struct or an array
func @f(%a: i32) {
  %s: i32 = agg.make %a @1:1
  func.ret
}
