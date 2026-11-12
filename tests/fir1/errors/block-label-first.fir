// error: 4:5: expected a block label like ^b but found %z
func @f() {
  cf.blocks {
    %z: i32 = int.const 0
  ^a:
    cf.yield
  }
  func.ret
}
