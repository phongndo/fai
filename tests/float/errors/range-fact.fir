// error: range.s(0, 1) is not a valid signed range for f32
func @f(%a: f32) -> f32 {
  %r: f32 [range.s(0, 1) assume] = copy %a
  func.ret %r
}
