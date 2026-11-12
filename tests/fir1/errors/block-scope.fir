// error: %i is not defined here
// A value defined in a block is visible only in that block; others get it as an argument.
func @f(%n: i32) -> i32 {
  %r: i32 = cf.blocks {
  ^entry:
    cf.br ^a(%n)
  ^a(%i: i32):
    cf.br ^b
  ^b:
    cf.yield %i
  }
  func.ret %r
}
