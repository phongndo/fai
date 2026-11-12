// error: malformed op
// A region on an op that has none.
func @f(%a: i32) -> i32 {
  %c: i32 = "copy"(%a) @4:3 ((%x: i32 [range.u(0, 9) check]) {
    %y: i32 = int.add.wrap %x, %x
    "cf.yield"(%y)
  }, {})
  func.ret %c
}
