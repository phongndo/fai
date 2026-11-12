// Variadic composites are C's: struct<C> and arrays, whose layout their values' shape gives.
// error: arguments of @g: struct<packed>{i8, i32} can't be a variadic argument
func @g(...) {
  func.ret
}

func @f(%s: struct<packed>{i8, i32}) {
  func.call @g(... %s)
  func.ret
}
