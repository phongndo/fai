// error: in @f: @?: cf.br can't leave a cf.try region
func @f() {
  cf.blocks {
  ^a:
    cf.try {
      cf.br ^b
    } catch(%e: ptr) {
      cf.yield
    }
    cf.br ^b
  ^b:
    cf.yield
  }
  func.ret
}
