// error: this op has no results
func @f(...) {
  %ap: ptr = mem.stack.of va_list, align 8
  %x: i32 = va.start %ap
  func.ret
}
