// error: a terminator must be the last op of its region
func @f(%a: i32) -> i32 {
  func.ret %a
  %b: i32 = int.const 1
  func.ret %b
}
