// error: mem.load needs the attribute 'align'
func @f(%p: ptr) -> i32 {
  %x: i32 = "mem.load"(%p)
  func.ret %x
}
