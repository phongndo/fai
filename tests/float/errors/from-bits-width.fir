// error: i64 and f32 have different widths
func @f(%a: i64) -> f32 {
  %r: f32 = float.from_bits %a
  func.ret %r
}
