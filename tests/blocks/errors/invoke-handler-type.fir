// error: in @f: @?: parameters of handler ^h: expected (ptr) but got (i32)
layer mfir
func @g() {
  func.ret
}
func @f() {
  cf.blocks {
  ^a:
    func.invoke @g() unwind ^h
    cf.yield
  ^h(%e: i32):
    cf.yield
  }
  func.ret
}
