// error: va_list can't be loaded: it is not a value type
func @f(%p: ptr) {
  %x: va_list = mem.load %p, align 8
  func.ret
}
