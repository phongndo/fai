// error: in @f: @?: cf.switch has more than one case 255
// Keys are taken modulo 2^N: -1 and 255 are the same i8.
func @f(%x: i8) {
  cf.blocks {
  ^entry:
    cf.switch %x, default ^a, [-1: ^a, 255: ^a]
  ^a:
    cf.yield
  }
  func.ret
}
