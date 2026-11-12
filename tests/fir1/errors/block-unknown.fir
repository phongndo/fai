// error: in @f: @4:5: no block ^nope in the enclosing cf.blocks
func @f() {
  cf.blocks {
  ^entry:
    cf.br ^nope @4:5
  }
  func.ret
}
