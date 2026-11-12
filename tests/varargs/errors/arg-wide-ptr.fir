// error: ptr can't be a variadic argument
// `va.arg` reads one 8-byte slot, so it can't read a pointer wider than 64 bits.
memspace default ptr 128 addr 64

func @first(...) -> ptr {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %p: ptr = va.arg %ap
  func.ret %p
}
