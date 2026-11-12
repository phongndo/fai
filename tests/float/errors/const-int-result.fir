// error: a float constant needs one float result
func @f() -> i32 {
  %r: i32 = float.const 1.5
  func.ret %r
}
