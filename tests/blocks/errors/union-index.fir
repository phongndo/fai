// A union has its variants only.
// error: @1:1: union<i32, ptr> has no variant 2
func @f(%u: union<i32, ptr>) {
  %x: i32 = union.get.trap %u, 2 @1:1
  func.ret
}
