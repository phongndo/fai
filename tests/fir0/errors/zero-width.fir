// error: i0 is not a valid type
func @f(%a: i0) -> i0 {
  func.ret %a
}
