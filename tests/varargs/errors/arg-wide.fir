// error: i128 can't be a variadic argument
func @f(...) -> i128 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %x: i128 = va.arg %ap
  func.ret %x
}
