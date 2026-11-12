// error: expected a %value but found '('
// A region's parameters are a parenthesized list of results.
func @f(%a: i32) -> i32 {
  %r: i32 = "cf.loop"(%a) {progress = false} (((%i: i32) {
    cf.break %i
  })
  func.ret %r
}
