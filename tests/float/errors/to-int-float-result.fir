// error: expected integers but got (f32)
func @f(%a: f64) -> f32 {
  %r: f32 = float.to_int.s.sat %a
  func.ret %r
}
