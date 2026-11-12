// error: f64 and i32 have different widths
func @f(%a: f64) -> i32 {
  %r: i32 = float.to_bits %a
  func.ret %r
}
