// A hole is a value not written yet. The program still verifies; running it stops at the hole.
// run: @scale(3) -> hole ?factor @2:3
func @scale(%x: i32) -> i32 {
  %y: i32 = int.mul.nsw %x, ?factor: i32 @2:3
  func.ret %y
}
