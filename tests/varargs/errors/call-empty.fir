// An empty struct can't be a variadic argument: no layout follows from its value.
// error: arguments of @g: struct<C>{} can't be a variadic argument
func @g(...) {
  func.ret
}

func @f(%s: struct<C>{}) {
  func.call @g(... %s)
  func.ret
}
