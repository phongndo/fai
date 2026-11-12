// error: operands: ptr can't be a variadic argument
memspace default ptr 128 addr 64

func @main(%f: ptr) {
  %p: ptr = mem.stack.of i32, align 4
  func.call.indirect func<(...)> %f(... %p)
  func.ret
}
