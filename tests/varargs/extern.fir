// Calls of variadic external functions (decision: Varargs): the event shows every argument, the
// variadic ones after the fixed ones. A va_list passed to an external function is memory it reads.
global const @fmt: array<4 x i8> = bytes "25640a00"

extern func @printf(ptr, ...) -> i32 effects[read(args), read(exposed), write(exposed), alloc, free, trap, diverge] assume
extern func @vprintf(ptr, ptr) -> i32 effects[read(args), read(exposed), write(exposed), alloc, free, trap, diverge] assume
extern func @log(ptr, ...) -> i32 effects[read(args)] assume
extern func @tick(...) effects[] assume
extern func @wide(i32, ...) -> i64 effects[] assume

// run: @hello() -> @printf(ptr #1, i32 7, f64 2.5, ptr null) -> i32 0; @tick() -> (); returned i32 0
// run: @forward(i32 9) -> @vprintf(ptr #1, ptr #3) -> i32 0; returned i32 0
// run: @indirect() -> @log(ptr #1, i64 3, i8 -1) -> i32 0; returned i32 0
// run: @many() -> @wide(i32 20, i64 1, f64 0.5, i64 2, f64 1.5, i64 3, f64 2.5, i64 4, f64 3.5, i64 5, f64 4.5, i64 6, f64 5.5, i64 7, f64 6.5, i64 8, f64 7.5, i64 9, f64 8.5, i64 10, f64 9.5) -> i64 0; returned i64 0
// run: @bad_sig() -> ub bad-call @48:3 (@tick has type func<(...)>)
// run: @bad_sig2() -> ub bad-call @54:3 (@sum has type func<(i32, ...) -> i32>)
func @hello() -> i32 {
  %f: ptr = mem.global @fmt
  %a: i32 = int.const 7
  %b: f64 = float.const 2.5
  %c: ptr = ptr.null
  %r: i32 = func.call @printf(%f, ... %a, %b, %c)
  func.call @tick(...)
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

func @indirect() -> i32 {
  %p: ptr = func.addr @log
  %f: ptr = mem.global @fmt
  %a: i64 = int.const 3
  %b: i8 = int.const -1
  %r: i32 = func.call.indirect func<(ptr, ...) -> i32> %p(%f, ... %a, %b)
  func.ret %r
}

// Calling a variadic function through a signature that isn't variadic, or the other way.
func @bad_sig() {
  %p: ptr = func.addr @tick
  func.call.indirect func<()> %p() @48:3
  func.ret
}

func @bad_sig2() -> i32 {
  %p: ptr = func.addr @sum
  %n: i32 = int.const 0
  %r: i32 = func.call.indirect func<(i32) -> i32> %p(%n) @54:3
  func.ret %r
}

func @sum(%n: i32, ...) -> i32 {
  func.ret %n
}

// More than eight variadic arguments of each class: the rest go on the stack.
func @many() -> i64 {
  %n: i32 = int.const 20
  %a1: i64 = int.const 1
  %a2: i64 = int.const 2
  %a3: i64 = int.const 3
  %a4: i64 = int.const 4
  %a5: i64 = int.const 5
  %a6: i64 = int.const 6
  %a7: i64 = int.const 7
  %a8: i64 = int.const 8
  %a9: i64 = int.const 9
  %a10: i64 = int.const 10
  %x1: f64 = float.const 0.5
  %x2: f64 = float.const 1.5
  %x3: f64 = float.const 2.5
  %x4: f64 = float.const 3.5
  %x5: f64 = float.const 4.5
  %x6: f64 = float.const 5.5
  %x7: f64 = float.const 6.5
  %x8: f64 = float.const 7.5
  %x9: f64 = float.const 8.5
  %x10: f64 = float.const 9.5
  %r: i64 = func.call @wide(%n, ... %a1, %x1, %a2, %x2, %a3, %x3, %a4, %x4, %a5, %x5, %a6, %x6, %a7, %x7, %a8, %x8, %a9, %x9, %a10, %x10)
  func.ret %r
}
