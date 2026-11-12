// error: 5:3: expected ':' but found ^b
func @f() {
  cf.blocks {
  ^a(%x: i32)
  ^b:
    cf.yield
  }
  func.ret
}
