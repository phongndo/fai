// error: operands: expected (ptr) but got (i64)
func @f(...) -> i32 {
  %n: i64 = int.const 0
  %x: i32 = va.arg %n
  func.ret %x
}
