// error: arguments of @g: expected (i32) but got (i64)
func @g(%x: i32) {
  func.ret
}

func @f(%y: i64) {
  func.call @g(%y)
  func.ret
}
