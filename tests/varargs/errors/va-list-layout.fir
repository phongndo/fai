// error: memspace: va_list size 0 must be positive and its alignment 3 a power of two
memspace default ptr 64 addr 64 valist 0:3

func @f() {
  func.ret
}
