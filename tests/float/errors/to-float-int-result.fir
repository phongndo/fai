// error: expected floats but got (i64)
func @f(%a: i64) -> i64 {
  %r: i64 = int.to_float.s %a
  func.ret %r
}
