// Variadic arguments under other data layouts (decision: Varargs): each takes one 8-byte slot,
// so 32-bit pointers fit with room to spare, and with 128-bit pointers the integers and floats
// still pass (a pointer can't: `errors/call-wide-ptr.fir`).

// run: @narrow_ptrs() -> returned i32 42, i64 7
memspace default ptr 32 addr 32

func @first(...) -> (i32, i64) {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %p: ptr = va.arg %ap
  %q: ptr = va.arg %ap
  %n: i64 = va.arg %ap
  %x: i32 = mem.load %p, align 4
  %y: i32 = mem.load %q, align 4
  %s: i32 = int.add.wrap %x, %y
  va.end %ap
  func.ret %s, %n
}

func @narrow_ptrs() -> (i32, i64) {
  %p: ptr = mem.stack.of i32, align 4
  %q: ptr = mem.stack.of i32, align 4
  %a: i32 = int.const 40
  %b: i32 = int.const 2
  mem.store i32 %a, %p, align 4
  mem.store i32 %b, %q, align 4
  %n: i64 = int.const 7
  %r: i32, %m: i64 = func.call @first(... %p, %q, %n)
  func.ret %r, %m
}
