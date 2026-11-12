// error: in @f: @?: a handler takes the exception only; unwind passes no arguments
layer mfir
func @g() {
  func.ret
}
func @f(%p: ptr) {
  cf.blocks {
  ^a:
    func.invoke @g() unwind ^h(%p)
    cf.yield
  ^h(%e: ptr):
    cf.yield
  }
  func.ret
}
