// error: 300 does not fit in i8
func @f() -> i8 {
  %b: i8 = int.const 300
  func.ret %b
}
