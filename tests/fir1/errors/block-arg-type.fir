// error: in @f: @?: arguments of ^a: expected (i32) but got (i64)
func @f(%x: i64) {
  cf.blocks {
  ^entry:
    cf.br ^a(%x)
  ^a(%y: i32):
    cf.yield
  }
  func.ret
}
