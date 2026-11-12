// error: expected an operand but found '...'
func @f(%a: i32) -> i32 {
  %b: i32 = int.add.wrap %a, ...
  func.ret %b
}
