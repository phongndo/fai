// Calls of variadic external functions (decision: Varargs): the event shows every argument, the
// variadic ones after the fixed ones. A va_list passed to an external function is memory it reads.
global const @fmt: array<4 x i8> = bytes "25640a00"

extern func @printf(ptr, ...) -> i32 effects[read(args), read(exposed), write(exposed), alloc, free, trap, diverge] assume
extern func @vprintf(ptr, ptr) -> i32 effects[read(args), read(exposed), write(exposed), alloc, free, trap, diverge] assume
extern func @none(...) effects[] assume

// run: @hello() -> @printf(ptr #1, i32 7, f64 2.5, ptr null) -> i32 0; @none() -> (); @none(i8 1) -> (); returned i32 0
// run: @forward(i32 9) -> @vprintf(ptr #1, ptr #3) -> i32 0; returned i32 0
// run: @indirect() -> @printf(ptr #1, i64 3) -> i32 0; @printf(ptr #1) -> i32 0; returned
// run: @bad_sig() -> ub bad-call @41:3 (@printf has type func<(ptr, ...) -> i32>)
// run: @bad_sig2() -> ub bad-call @47:3 (@sum has type func<(i32, ...) -> i32>)
func @hello() -> i32 {
  %f: ptr = mem.global @fmt
  %a: i32 = int.const 7
  %b: f64 = float.const 2.5
  %c: ptr = ptr.null
  %r: i32 = func.call @printf(%f, ... %a, %b, %c)
  func.call @none(...)
  %d: i8 = int.const 1
  func.call @none(... %d)
  func.ret %r
}

func @forward(...) -> i32 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %f: ptr = mem.global @fmt
  %r: i32 = func.call @vprintf(%f, %ap)
  va.end %ap
  func.ret %r
}

func @indirect() {
  %p: ptr = func.addr @printf
  %f: ptr = mem.global @fmt
  %a: i64 = int.const 3
  %r: i32 = func.call.indirect func<(ptr, ...) -> i32> %p(%f, ... %a)
  %s: i32 = func.call.indirect func<(ptr, ...) -> i32> %p(%f, ...)
  func.ret
}

// Calling a variadic function through a signature that isn't variadic, or the other way.
func @bad_sig() -> i32 {
  %p: ptr = func.addr @printf
  %f: ptr = mem.global @fmt
  %r: i32 = func.call.indirect func<(ptr) -> i32> %p(%f) @41:3
  func.ret %r
}

func @bad_sig2() -> i32 {
  %p: ptr = func.addr @sum
  %n: i32 = int.const 0
  %r: i32 = func.call.indirect func<(i32) -> i32> %p(%n) @47:3
  func.ret %r
}

func @sum(%n: i32, ...) -> i32 {
  func.ret %n
}
