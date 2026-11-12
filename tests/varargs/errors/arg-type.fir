// error: i1 can't be a variadic argument
func @f(...) -> i1 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %x: i1 = va.arg %ap
  func.ret %x
}
