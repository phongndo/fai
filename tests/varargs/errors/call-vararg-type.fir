// error: arguments of @g: i1 can't be a variadic argument
func @g(...) {
  func.ret
}

func @f() {
  %b: i1 = int.const 1
  func.call @g(... %b)
  func.ret
}
