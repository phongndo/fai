// error: expected integers but got (f32)
func @f(%a: f32) -> f32 {
  %r: f32 = int.add.wrap %a, %a
  func.ret %r
}
