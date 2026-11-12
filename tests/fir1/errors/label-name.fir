// error: 4:13: expected a name after '^'
func @f() {
  cf.blocks {
  ^a: cf.br ^ (%x)
  }
  func.ret
}
