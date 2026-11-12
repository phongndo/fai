// error: in @f: @5:5: a terminator must be the last op of its region
func @f() {
  cf.blocks {
  ^a:
    cf.br ^b @5:5
    %z: i32 = int.const 0
  ^b:
    cf.yield
  }
  func.ret
}
