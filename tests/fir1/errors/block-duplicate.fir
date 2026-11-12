// error: in @f: @3:3: block ^a is defined more than once
func @f() {
  cf.blocks @3:3 {
  ^a:
    cf.br ^a
  ^a:
    cf.yield
  }
  func.ret
}
