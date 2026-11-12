// error: no block ^out in the enclosing cf.blocks
// A jump names a block of the nearest cf.blocks only.
func @f() {
  cf.blocks {
  ^entry:
    cf.blocks {
    ^inner:
      cf.br ^out
    }
    cf.br ^out
  ^out:
    cf.yield
  }
  func.ret
}
