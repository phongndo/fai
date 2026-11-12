// error: expected (i64) but got (i32)
func @f(%x: i64) -> i32 {
  %y: i32 = copy %x
  func.ret %y
}
