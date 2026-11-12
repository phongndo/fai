// error: unknown op 'float.to_int.s'
func @f(%a: f64) -> i32 {
  %r: i32 = float.to_int.s %a
  func.ret %r
}
