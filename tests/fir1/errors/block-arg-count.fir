// error: in @f: @?: arguments of ^a: expected (i32) but got ()
func @f(%c: i1) {
  cf.blocks {
  ^entry:
    %z: i32 = int.const 0
    cf.cond_br %c, ^a(%z), ^a
  ^a(%y: i32):
    cf.yield
  }
  func.ret
}
