// error: in @f: @?: no block ^nope in the enclosing cf.blocks
layer mfir
func @g() {
  func.ret
}
func @f() {
  cf.blocks {
  ^a:
    func.invoke @g() unwind ^nope
    cf.yield
  }
  func.ret
}
