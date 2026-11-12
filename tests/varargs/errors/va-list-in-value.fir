// error: struct<C>{i32, va_list} is not a value type
func @f(%s: struct<C>{i32, va_list}) {
  func.ret
}
