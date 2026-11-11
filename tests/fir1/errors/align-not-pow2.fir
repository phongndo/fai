// error: alignment must be a power of two
func @f() {
  %p: ptr = mem.stack 4, align 3
  func.ret
}
