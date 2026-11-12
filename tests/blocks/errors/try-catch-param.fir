// error: in @f: @?: the catch region of cf.try takes one parameter, the exception, a ptr
func @f() {
  cf.try {
    cf.yield
  } catch(%e: i32) {
    cf.yield
  }
  func.ret
}
