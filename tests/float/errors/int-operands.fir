// error: expected floats but got (i32)
func @f(%a: i32) -> i32 {
  %r: i32 = float.add %a, %a
  func.ret %r
}
