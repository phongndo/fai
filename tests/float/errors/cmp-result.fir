// error: results: expected (i1) but got (f32)
func @f(%a: f32) -> f32 {
  %r: f32 = float.cmp.olt %a, %a
  func.ret %r
}
