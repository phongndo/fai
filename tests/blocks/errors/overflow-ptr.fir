// Checked arithmetic is on integers.
// error: @1:1: expected integers but got (ptr)
func @f(%a: ptr) {
  %r: ptr, %o: i1 = int.mul.overflow.u %a, %a @1:1
  func.ret
}
