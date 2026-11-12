// error: 4294967296 is not the bits of a f32
func @f() -> f32 {
  %r: f32 = "float.const"() {value = 4294967296}
  func.ret %r
}
