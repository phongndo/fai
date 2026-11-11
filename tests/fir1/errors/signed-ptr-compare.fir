// error: pointer comparisons are unsigned
func @f(%p: ptr, %q: ptr) -> i1 {
  %c: i1 = ptr.cmp.slt %p, %q
  func.ret %c
}
