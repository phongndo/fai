// What `va.arg` leaves undefined (decision: Varargs): reading past the last variadic argument, an
// argument of the other class (an integer as a float or back), a va_list that holds no cursor (never
// started, ended, or written over), and the variadic arguments of a call that has returned.

// run: @past(i64 1) -> ub va-arg @14:8 (no variadic argument is left: the call passed 1)
// run: @past() -> ub va-arg @13:8 (no variadic argument is left: the call passed 0)
// run: @class(f64 1.5) -> ub va-arg @19:8 (variadic argument 0 has type f64, of the other class than i64)
// run: @class(ptr null) -> returned i64 0
// run: @class(i32 3) -> returned i64 poison
// run: @fclass(i64 1) -> ub va-arg @25:8 (variadic argument 0 has type i64, of the other class than f32)
// run: @fclass(f64 1.5) -> returned f32 0.0
// run: @unstarted(i64 1) -> ub va-arg @25:8 (the va_list holds no cursor from va.start)
// run: @ended(i64 1) -> ub va-arg @32:8 (the va_list holds no cursor from va.start)
// run: @clobbered(i64 1) -> ub va-arg @41:8 (the va_list holds no cursor from va.start)
// run: @dangling() -> ub use-after-free @62:8 (the variadic arguments of a call from @57:8, which has returned)
// run: @peek(i64 5) -> returned i64 poison, i32 poison, b16 (va(#1, 0)[24], va(#1, 0)[25])
func @past(...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: i64 = va.arg %ap @13:8
  %b: i64 = va.arg %ap @14:8
  func.ret %b
}

func @class(...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: i64 = va.arg %ap @19:8
  func.ret %a
}

func @fclass(...) -> f32 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: f32 = va.arg %ap @25:8
  func.ret %a
}

func @unstarted(...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  %a: i64 = va.arg %ap @25:8
  func.ret %a
}

func @ended(...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  va.end %ap
  %a: i64 = va.arg %ap @32:8
  func.ret %a
}

// Writing any byte of a va_list ends its cursor.
func @clobbered(...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %z: i32 = int.const 0
  %off: i64 = int.const 24
  %q: ptr = ptr.offset.inbounds %ap, %off
  mem.store i32 %z, %q, align 4
  %a: i64 = va.arg %ap @41:8
  func.ret %a
}

func @keep(%out: ptr, ...) {
  va.start %out
  func.ret
}

func @dangling() -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  %a: i64 = int.const 1
  func.call @keep(%ap, ... %a) @57:8
  %x: i64 = va.arg %ap @62:8
  func.ret %x
}

// The bytes of a va_list mean nothing to loads: they read as poison, and as bytes they are the
// cursor's, which any bytes refine (decision: va_list).
func @peek(...) -> (i64, i32, b16) {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: i64 = mem.load %ap, align 8
  %off: i64 = int.const 24
  %q: ptr = ptr.offset.inbounds %ap, %off
  %b: i32 = mem.load %q, align 4
  %c: b16 = mem.load %q, align 2
  func.ret %a, %b, %c
}
