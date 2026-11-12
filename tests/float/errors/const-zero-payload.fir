// error: the NaN payload doesn't fit f64
func @f() -> f64 {
  %r: f64 = float.const -nan(0x0)
  func.ret %r
}
