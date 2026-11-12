// error: unknown op 'float.rem'
func @f(%a: f64) -> f64 {
  %r: f64 = float.rem %a, %a
  func.ret %r
}
