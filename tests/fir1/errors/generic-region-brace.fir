// error: expected '{' but found @f
// Each region in a generic op's list needs its braces.
func @f(%c: i1, %a: i32) -> i32 {
  %r: i32 = "cf.if"(%c) ({
    cf.yield %a
  }, @f)
  func.ret %r
}
