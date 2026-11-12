// error: arguments of @g: expected (i32) but got (i64)
func @g(%n: i32, ...) {
  func.ret
}

func @f() {
  %a: i64 = int.const 1
  func.call @g(%a, ...)
  func.ret
}
