// error: in @f: @?: cf.cond_br condition: expected (i1) but got (i32)
func @f(%x: i32) {
  cf.blocks {
  ^entry:
    cf.cond_br %x, ^a, ^a
  ^a:
    cf.yield
  }
  func.ret
}
