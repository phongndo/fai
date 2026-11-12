// error: @g is variadic: write '...' after its 1 fixed arguments
func @g(%n: i32, ...) {
  func.ret
}

func @f() {
  %a: i32 = int.const 1
  func.call @g(... %a, %a)
  func.ret
}
