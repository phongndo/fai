// error: in @f: @?: cf.switch value: expected an integer but got ptr
func @f(%p: ptr) {
  cf.blocks {
  ^entry:
    cf.switch %p, default ^a, []
  ^a:
    cf.yield
  }
  func.ret
}
