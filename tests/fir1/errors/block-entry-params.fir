// error: in @f: @?: the entry block of cf.blocks has no parameters
func @f() {
  cf.blocks {
  ^entry(%x: i32):
    cf.yield
  }
  func.ret
}
