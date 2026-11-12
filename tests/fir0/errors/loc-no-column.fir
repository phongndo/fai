// error: 4:15: expected a column number in a location
func @f() -> i32 {
  %x: i32 = int.const 1
  func.ret %x @4:
}
