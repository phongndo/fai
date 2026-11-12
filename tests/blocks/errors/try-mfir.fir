// error: in @f: @?: cf.try is not allowed in layer mfir; it is allowed in hfir
layer mfir
func @f() {
  cf.try {
    cf.yield
  } catch(%e: ptr) {
    cf.yield
  }
  func.ret
}
