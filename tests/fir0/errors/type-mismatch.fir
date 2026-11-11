// error: expected (i32) but got (i64)
func @f(%a: i32, %b: i64) -> i32 {
  %r: i32 = int.add.wrap %a, %b
  func.ret %r
}
