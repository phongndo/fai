// error: in @f: @?: func.invoke is not allowed in layer hfir; it is allowed in mfir
func @g() {
  func.ret
}
func @f() {
  cf.blocks {
  ^a:
    func.invoke @g() unwind ^h
    cf.yield
  ^h(%e: ptr):
    cf.yield
  }
  func.ret
}
