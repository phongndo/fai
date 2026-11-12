// error: arguments of @g: struct<C>{i32, i32} can't be a variadic argument
func @g(...) {
  func.ret
}

func @f(%s: struct<C>{i32, i32}) {
  func.call @g(... %s)
  func.ret
}
