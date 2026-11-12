// With 128-bit pointers (CHERI's layout), integers and floats still pass as variadic arguments,
// one 8-byte slot each; a pointer can't (decision: Varargs; `errors/call-wide-ptr.fir`), so a
// frontend passes its address, or the pointer through memory.

// run: @wide() -> returned i64 42, f64 2.5, i32 9
memspace default ptr 128 addr 64

func @first(...) -> (i64, f64, i32) {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %n: i64 = va.arg %ap
  %x: f64 = va.arg %ap
  %a: i64 = va.arg %ap
  va.end %ap
  %q: ptr = ptr.from_exposed %a
  %y: i32 = mem.load %q, align 4
  func.ret %n, %x, %y
}

func @wide() -> (i64, f64, i32) {
  %n: i64 = int.const 42
  %x: f64 = float.const 2.5
  %p: ptr = mem.stack.of i32, align 4
  %v: i32 = int.const 9
  mem.store i32 %v, %p, align 4
  %a: i64 = ptr.expose %p
  %r: i64, %s: f64, %t: i32 = func.call @first(... %n, %x, %a)
  func.ret %r, %s, %t
}
