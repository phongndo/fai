// error: attribute 'align' is given twice
func @f(%p: ptr) -> i32 {
  %x: i32 = "mem.load"(%p) {align = 4, align = 8}
  func.ret %x
}
