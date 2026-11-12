// error: cannot truncate f32 to f64
func @f(%a: f32) -> f64 {
  %r: f64 = float.trunc %a
  func.ret %r
}
