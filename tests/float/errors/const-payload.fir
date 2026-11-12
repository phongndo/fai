// error: the NaN payload doesn't fit f32
func @f() -> f32 {
  %r: f32 = float.const nan(0x800000)
  func.ret %r
}
