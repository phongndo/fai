// union.make takes a value of the variant's type.
// error: @1:1: variant 0 of union<i32, ptr>: expected (i32) but got (ptr)
func @f(%a: ptr) {
  %u: union<i32, ptr> = union.make %a, 0 @1:1
  func.ret
}
