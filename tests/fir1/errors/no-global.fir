// mem.global names a global.
// error: in @f: @?: no global @f
func @f() -> ptr {
  %p: ptr = mem.global @f
  func.ret %p
}
