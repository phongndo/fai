// error: in @f: @?: cf.switch outside cf.blocks
func @f(%x: i32, %c: i1) {
  cf.if %c {
    cf.switch %x, default ^a, []
  }
  func.ret
}
