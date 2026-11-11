// FIR has no default overflow behavior: `int.add` must say what overflow does.
// error: unknown op 'int.add'
func @f(%a: i32) -> i32 {
  %r: i32 = int.add %a, %a
  func.ret %r
}
