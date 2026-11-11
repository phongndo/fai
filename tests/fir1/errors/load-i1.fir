// error: i1 can't be loaded: its size isn't whole bytes
func @f(%p: ptr) -> i1 {
  %x: i1 = mem.load %p, align 1
  func.ret %x
}
