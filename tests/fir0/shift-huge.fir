// Shifting by at least the width: .total gives 0 (or the sign for shr.s), however large the amount.
// run: @shl(1, 4294967296) -> returned i64 0
// run: @shr_s(-8, 18446744073709551615) -> returned i64 -1
func @shl(%x: i64, %n: i64) -> i64 {
  %r: i64 = int.shl.total %x, %n
  func.ret %r
}

func @shr_s(%x: i64, %n: i64) -> i64 {
  %r: i64 = int.shr.s.total %x, %n
  func.ret %r
}
