// error: cf.loop initial values: expected (i32) but got (i32, i32)
// Two initial values for one loop parameter.
func @f(%a: i32) -> i32 {
  %r: i32 = "cf.loop"(%a, %a) {progress = false} ((%i: i32) {
    cf.break %i
  })
  func.ret %r
}
