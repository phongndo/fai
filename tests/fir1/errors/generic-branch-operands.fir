// error: in @f: @?: malformed op
// The operands are the branch's own, then each target's arguments: 1 + 1 + 0 here, not 2.
func @f(%c: i1, %x: i32) {
  cf.blocks {
  ^entry:
    "cf.cond_br"(%c, %x, %x) {t = ^a(1), f = ^b}
  ^a(%y: i32):
    cf.yield
  ^b:
    cf.yield
  }
  func.ret
}
