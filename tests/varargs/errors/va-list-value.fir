// error: va_list is not a value type
func @f(%ap: va_list) {
  func.ret
}
