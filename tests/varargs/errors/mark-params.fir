// error: '...' must come after the parameters
func @g(..., %n: i32) {
  func.ret
}
