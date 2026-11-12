// Arrays are written array<N x T>.
// error: 4:28: expected 'x'
func @f() -> i64 {
  %n: i64 = ty.size array<4, i32>
  func.ret %n
}
