// error: unknown op 'int.add'
// The generic form's name carries the op's modifiers, as the readable form's does.
func @f(%a: i32) -> i32 {
  %s: i32 = "int.add"(%a, %a)
  func.ret %s
}
