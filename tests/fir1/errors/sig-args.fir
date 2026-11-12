// An indirect call passes the signature's arguments.
// error: in @f: @?: operands: expected (ptr, i32) but got (ptr, i64)
func @f(%p: ptr, %x: i64) -> i32 {
  %r: i32 = func.call.indirect func<(i32) -> i32> %p(%x)
  func.ret %r
}
