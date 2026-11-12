// error: in @f: @?: cf.yield: expected (i32) but got ()
func @f() -> i32 {
  %r: i32 = cf.blocks {
  ^a:
    cf.yield
  }
  func.ret %r
}
