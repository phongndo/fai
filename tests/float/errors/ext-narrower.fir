// error: cannot extend f64 to f32
func @f(%a: f64) -> f32 {
  %r: f32 = float.ext %a
  func.ret %r
}
