// error: va.start is only allowed in a variadic function
func @f(%n: i32) {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  func.ret
}
