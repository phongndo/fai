// error: operands: expected (f32) but got (f64)
func @f(%a: f32, %b: f64) -> f32 {
  %r: f32 = float.mul %a, %b
  func.ret %r
}
