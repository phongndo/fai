// error: range.s(5, 200) is not a valid signed range for i8
func @f(%a: i8) -> i8 {
  %b: i8 [range.s(5, 200) assume] = freeze %a
  func.ret %b
}
