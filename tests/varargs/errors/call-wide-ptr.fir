// error: arguments of @first: ptr can't be a variadic argument
// A variadic argument takes one 8-byte slot, so a pointer wider than 64 bits can't be one
// (decision: Varargs).
memspace default ptr 128 addr 64

func @first(...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %x: i64 = va.arg %ap
  func.ret %x
}

func @main() -> i64 {
  %p: ptr = mem.stack.of i32, align 4
  %r: i64 = func.call @first(... %p)
  func.ret %r
}
