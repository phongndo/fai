// error: in @f: @?: the catch region of cf.try takes one parameter, the exception, a ptr
func @f() {
  cf.try {
    cf.yield
  }
  func.ret
}
