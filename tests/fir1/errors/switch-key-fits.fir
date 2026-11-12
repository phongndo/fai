// error: in @f: @?: 300 does not fit in i8
func @f(%x: i8) {
  cf.blocks {
  ^entry:
    cf.switch %x, default ^a, [300: ^a]
  ^a:
    cf.yield
  }
  func.ret
}
