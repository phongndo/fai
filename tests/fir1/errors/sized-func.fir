// Function types have no size.
// error: in @f: @?: func<(i32) -> i32> has no size in memory
func @f() -> i64 {
  %n: i64 = ty.size func<(i32) -> i32>
  func.ret %n
}
