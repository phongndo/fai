// Structs and arrays as variadic arguments (decisions: Varargs, C ABI for aggregates): C passes
// them to `...` as named arguments of their types, and `va.arg T` reads one back by AAPCS64's
// algorithm: up to 16 bytes from the general-purpose save area or the stack, an HFA from the FP
// save area (a 16-byte slot per member) or the stack, a larger one through the pointer passed.
// `va.arg` must ask for the argument's type, up to an array being the struct of its elements.

extern func @vlog(i32, ...) -> i32 effects[] assume

// Reads, in order: a two-word struct, an HFA of three doubles, a large struct, an i64, a
// one-word struct, an HFA of two floats.
func @take(%n: i32, ...) -> struct<C>{i64, f64, i64, i64, i32, f32} {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: struct<C>{i64, i32} = va.arg %ap
  %b: struct<C>{f64, f64, f64} = va.arg %ap
  %c: struct<C>{i64, i64, i64, i64} = va.arg %ap
  %d: i64 = va.arg %ap
  %e: array<2 x i16> = va.arg %ap
  %f: struct<C>{f32, f32} = va.arg %ap
  va.end %ap
  %a0: i64 = agg.extract %a, 0
  %a1: i32 = agg.extract %a, 1
  %b2: f64 = agg.extract %b, 2
  %c3: i64 = agg.extract %c, 3
  %e1: i16 = agg.extract %e, 1
  %e32: i32 = int.sext %e1
  %ae: i32 = int.add.wrap %a1, %e32
  %f1: f32 = agg.extract %f, 1
  %r: struct<C>{i64, f64, i64, i64, i32, f32} = agg.make %a0, %b2, %c3, %d, %ae, %f1
  func.ret %r
}

func @args() -> (struct<C>{i64, i32}, struct<C>{f64, f64, f64}, struct<C>{i64, i64, i64, i64}, i64, struct<C>{i16, i16}, struct<C>{f32, f32}) {
  %x: i64 = int.const 77
  %y: i32 = int.const -5
  %a: struct<C>{i64, i32} = agg.make %x, %y
  %p: f64 = float.const 2.5
  %q: f64 = float.const -1.0
  %b: struct<C>{f64, f64, f64} = agg.make %p, %p, %q
  %c: struct<C>{i64, i64, i64, i64} = agg.make %x, %x, %x, %x
  %s: i16 = int.const 300
  %e: struct<C>{i16, i16} = agg.make %s, %s
  %g: f32 = float.const 0.5
  %f: struct<C>{f32, f32} = agg.make %g, %g
  func.ret %a, %b, %c, %x, %e, %f
}

func @call_take() -> struct<C>{i64, f64, i64, i64, i32, f32} {
  %a: struct<C>{i64, i32}, %b: struct<C>{f64, f64, f64}, %c: struct<C>{i64, i64, i64, i64}, %x: i64, %e: struct<C>{i16, i16}, %f: struct<C>{f32, f32} = func.call @args()
  %n: i32 = int.const 6
  %r: struct<C>{i64, f64, i64, i64, i32, f32} = func.call @take(%n, ... %a, %b, %c, %x, %e, %f)
  func.ret %r
}

// After eight integer arguments and seven doubles the composites are all on the stack, and an
// HFA that doesn't fit the FP registers left sends every float after it there too.
func @late(%n: i32, ...) -> (f64, i64, f32) {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %acc: f64 = float.const 0.0
  %i0: i64 = va.arg %ap
  %i1: i64 = va.arg %ap
  %i2: i64 = va.arg %ap
  %i3: i64 = va.arg %ap
  %i4: i64 = va.arg %ap
  %i5: i64 = va.arg %ap
  %i6: i64 = va.arg %ap
  %d0: f64 = va.arg %ap
  %d1: f64 = va.arg %ap
  %d2: f64 = va.arg %ap
  %d3: f64 = va.arg %ap
  %d4: f64 = va.arg %ap
  %d5: f64 = va.arg %ap
  %h: struct<C>{f64, f64, f64} = va.arg %ap
  %z: f64 = va.arg %ap
  %w: struct<C>{i64, i64} = va.arg %ap
  %v: struct<C>{f32, i8} = va.arg %ap
  va.end %ap
  %h1: f64 = agg.extract %h, 1
  %t: f64 = float.add %h1, %z
  %w1: i64 = agg.extract %w, 1
  %u: i64 = int.add.wrap %w1, %i6
  %v0: f32 = agg.extract %v, 0
  func.ret %t, %u, %v0
}

func @call_late() -> (f64, i64, f32) {
  %n: i32 = int.const 0
  %i: i64 = int.const 3
  %d: f64 = float.const 0.25
  %h0: f64 = float.const 8.0
  %h: struct<C>{f64, f64, f64} = agg.make %h0, %h0, %h0
  %w: struct<C>{i64, i64} = agg.make %i, %i
  %f: f32 = float.const -6.5
  %c: i8 = int.const 1
  %v: struct<C>{f32, i8} = agg.make %f, %c
  %t: f64, %u: i64, %x: f32 = func.call @late(%n, ... %i, %i, %i, %i, %i, %i, %i, %d, %d, %d, %d, %d, %d, %h, %d, %w, %v)
  func.ret %t, %u, %x
}

// To C: an external variadic function sees the composites as values.
func @to_c() -> i32 {
  %n: i32 = int.const 2
  %x: f32 = float.const 1.0
  %s: struct<C>{f32, f32} = agg.make %x, %x
  %c: i8 = int.const -1
  %t: array<3 x i8> = agg.make %c, %c, %c
  %r: i32 = func.call @vlog(%n, ... %s, %t)
  func.ret %r
}

// `va.arg` must ask for the argument's type: a struct of other fields, or a scalar, is UB.
func @wrong(...) -> struct<C>{i32, i32} {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: struct<C>{i32, i32} = va.arg %ap @116:3
  func.ret %a
}

func @call_wrong(%k: i32) -> struct<C>{i32, i32} {
  %x: i64 = int.sext %k
  %s: struct<C>{i64} = agg.make %x
  %r: struct<C>{i32, i32} = func.call @wrong(... %s)
  func.ret %r
}

func @scalar(...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: i64 = va.arg %ap @130:3
  func.ret %a
}

func @call_scalar(%k: i64) -> i64 {
  %s: struct<C>{i64} = agg.make %k
  %r: i64 = func.call @scalar(... %s)
  func.ret %r
}

// An array is read as the struct of its elements, and the other way.
func @arr(...) -> array<2 x i32> {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: array<2 x i32> = va.arg %ap
  func.ret %a
}

func @call_arr(%k: i32) -> array<2 x i32> {
  %s: struct<C>{i32, i32} = agg.make %k, %k
  %r: array<2 x i32> = func.call @arr(... %s)
  func.ret %r
}

// run: @call_take() -> returned {i64 77, f64 -1.0, i64 77, i64 77, i32 295, f32 0.5}
// run: @call_late() -> returned f64 8.25, i64 6, f32 -6.5
// run: @to_c() -> @vlog(i32 2, {f32 1.0, f32 1.0}, {i8 -1, i8 -1, i8 -1}) -> i32 0; returned i32 0
// run: @call_wrong(1) -> ub va-arg @116:3 (variadic argument 0 has type struct<C>{i64}, not struct<C>{i32, i32})
// run: @call_scalar(1) -> ub va-arg @130:3 (variadic argument 0 has type struct<C>{i64}, not i64)
// run: @call_arr(7) -> returned {i32 7, i32 7}
