// error: in @f: @?: cf.blocks needs at least one block
func @f() {
  cf.blocks {
  }
  func.ret
}
