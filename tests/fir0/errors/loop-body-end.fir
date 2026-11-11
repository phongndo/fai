// error: a loop body must end with cf.break or cf.continue
func @f() {
  cf.loop {
    %x: i32 = int.const 1
  }
  func.ret
}
