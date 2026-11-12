// error: expected a float like 1.5, inf, or nan but found 'pi'
func @f() -> f64 {
  %r: f64 = float.const pi
  func.ret %r
}
