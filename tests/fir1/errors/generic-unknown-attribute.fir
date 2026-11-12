// error: int.add.nsw has no attribute 'align'
// Attributes are the op's immediates; int.add has none.
func @f(%a: i32, %b: i32) -> i32 {
  %s: i32 = "int.add.nsw"(%a, %b) {align = 4}
  func.ret %s
}
