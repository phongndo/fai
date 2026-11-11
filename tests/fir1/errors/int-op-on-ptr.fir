// error: expected integers but got (ptr)
func @f(%p: ptr) -> ptr {
  %q: ptr = int.add.wrap %p, %p
  func.ret %q
}
