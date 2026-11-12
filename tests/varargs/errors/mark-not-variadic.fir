// error: @g is not variadic: '...' marks variadic arguments
func @g(%n: i32) {
  func.ret
}

func @f() {
  %a: i32 = int.const 1
  func.call @g(%a, ...)
  func.ret
}
