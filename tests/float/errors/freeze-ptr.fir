// error: expected integers or floats but got (ptr)
func @f(%a: ptr) -> ptr {
  %r: ptr = freeze %a
  func.ret %r
}
