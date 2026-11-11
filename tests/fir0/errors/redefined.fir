// error: %x is defined more than once
func @f(%x: i32) -> i32 {
  %x: i32 = int.const 1
  func.ret %x
}
