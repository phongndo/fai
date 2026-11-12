// Structs and arrays by value in the C ABI (decision: C ABI for aggregates): every AAPCS64
// class as a parameter and as a result, between FIR functions and to C (external functions,
// whose arguments the world sees as values). HFIR passes composites whole; on AArch64 an HFA
// travels in FP registers, up to 16 bytes in one or two x registers, more as a pointer to a copy,
// and a result where it would be passed first or at x8.

extern func @see(struct<C>{f32, f32, f32}, struct<C>{i8, i32}, struct<C>{i64, ptr, i64}, struct<C>{f64}) -> struct<C>{i32, f32} effects[] assume

// HFAs of one to four members, f32 and f64, with arrays inside.
func @hfa_f32(%a: struct<C>{f32}, %b: struct<C>{f32, f32}, %c: struct<C>{f32, array<2 x f32>}, %d: array<4 x f32>) -> struct<C>{f32, f32, f32, f32} {
  %a0: f32 = agg.extract %a, 0
  %b1: f32 = agg.extract %b, 1
  %c1: array<2 x f32> = agg.extract %c, 1
  %c11: f32 = agg.extract %c1, 1
  %d3: f32 = agg.extract %d, 3
  %r: struct<C>{f32, f32, f32, f32} = agg.make %d3, %c11, %b1, %a0
  func.ret %r
}

func @hfa_f64(%a: struct<C>{f64}, %b: array<2 x f64>, %c: struct<C>{struct<C>{f64}, f64, f64}, %d: struct<C>{f64, f64, f64, f64}) -> struct<C>{f64, f64, f64} {
  %a0: f64 = agg.extract %a, 0
  %b0: f64 = agg.extract %b, 0
  %c2: f64 = agg.extract %c, 2
  %d1: f64 = agg.extract %d, 1
  %s: f64 = float.add %a0, %b0
  %r: struct<C>{f64, f64, f64} = agg.make %s, %c2, %d1
  func.ret %r
}

func @hfas() -> (struct<C>{f32, f32, f32, f32}, struct<C>{f64, f64, f64}) {
  %x: f32 = float.const 1.5
  %y: f32 = float.const -2.25
  %z: f32 = float.const 3.0
  %w: f32 = float.const 0.125
  %a: struct<C>{f32} = agg.make %x
  %b: struct<C>{f32, f32} = agg.make %x, %y
  %two: array<2 x f32> = agg.make %z, %w
  %c: struct<C>{f32, array<2 x f32>} = agg.make %y, %two
  %d: array<4 x f32> = agg.make %w, %z, %y, %x
  %r: struct<C>{f32, f32, f32, f32} = func.call @hfa_f32(%a, %b, %c, %d)
  %p: f64 = float.const 0.5
  %q: f64 = float.const 1e300
  %n: f64 = float.const -0.0
  %e: struct<C>{f64} = agg.make %p
  %f: array<2 x f64> = agg.make %q, %n
  %g0: struct<C>{f64} = agg.make %n
  %g: struct<C>{struct<C>{f64}, f64, f64} = agg.make %g0, %p, %q
  %h: struct<C>{f64, f64, f64, f64} = agg.make %p, %q, %n, %p
  %s: struct<C>{f64, f64, f64} = func.call @hfa_f64(%e, %f, %g, %h)
  func.ret %r, %s
}

func @hfa4_out() -> struct<C>{f32, f32, f32, f32} {
  %r: struct<C>{f32, f32, f32, f32}, %s: struct<C>{f64, f64, f64} = func.call @hfas()
  func.ret %r
}

func @hfa3_out() -> struct<C>{f64, f64, f64} {
  %r: struct<C>{f32, f32, f32, f32}, %s: struct<C>{f64, f64, f64} = func.call @hfas()
  func.ret %s
}

// Composites of 1 to 16 bytes in x registers: padding, floats mixed with integers, a pointer,
// a 16-byte aligned struct, packed fields that straddle words.
func @small(%a: struct<C>{i8}, %b: struct<C>{i8, i16}, %c: struct<C>{i8, i32}, %d: struct<C>{i32, f32}, %e: struct<C>{f32, i32, i8}, %f: struct<C>{i64, i8}, %g: struct<packed>{i8, i64}) -> struct<C>{i64, i32, i16, i8} {
  %a0: i8 = agg.extract %a, 0
  %b1: i16 = agg.extract %b, 1
  %c1: i32 = agg.extract %c, 1
  %d1: f32 = agg.extract %d, 1
  %d1i: i32 = float.to_bits %d1
  %e2: i8 = agg.extract %e, 2
  %f0: i64 = agg.extract %f, 0
  %g1: i64 = agg.extract %g, 1
  %g0: i8 = agg.extract %g, 0
  %s0: i64 = int.add.wrap %f0, %g1
  %s1: i32 = int.add.wrap %c1, %d1i
  %bb: i16 = int.sext %a0
  %s2: i16 = int.add.wrap %b1, %bb
  %s3: i8 = int.add.wrap %e2, %g0
  %r: struct<C>{i64, i32, i16, i8} = agg.make %s0, %s1, %s2, %s3
  func.ret %r
}

func @smalls() -> struct<C>{i64, i32, i16, i8} {
  %n8: i8 = int.const -7
  %n16: i16 = int.const 300
  %n32: i32 = int.const 100000
  %n64: i64 = int.const 4000000000
  %f: f32 = float.const 1.0
  %a: struct<C>{i8} = agg.make %n8
  %b: struct<C>{i8, i16} = agg.make %n8, %n16
  %c: struct<C>{i8, i32} = agg.make %n8, %n32
  %d: struct<C>{i32, f32} = agg.make %n32, %f
  %e: struct<C>{f32, i32, i8} = agg.make %f, %n32, %n8
  %ff: struct<C>{i64, i8} = agg.make %n64, %n8
  %g: struct<packed>{i8, i64} = agg.make %n8, %n64
  %r: struct<C>{i64, i32, i16, i8} = func.call @small(%a, %b, %c, %d, %e, %ff, %g)
  func.ret %r
}

// A result of each size up to 16 bytes, odd ones included.
func @r3(%x: i8) -> array<3 x i8> {
  %y: i8 = int.add.wrap %x, %x
  %r: array<3 x i8> = agg.make %x, %y, %x
  func.ret %r
}

func @r12(%x: i32) -> struct<C>{i32, f32, i32} {
  %f: f32 = int.to_float.s %x
  %r: struct<C>{i32, f32, i32} = agg.make %x, %f, %x
  func.ret %r
}

func @r16(%p: ptr, %x: i64) -> struct<C>{ptr, i64} {
  %r: struct<C>{ptr, i64} = agg.make %p, %x
  func.ret %r
}

func @mixed2(%x: f32, %y: f64) -> struct<C>{f32, f64} {
  %r: struct<C>{f32, f64} = agg.make %x, %y
  func.ret %r
}

// A 16-byte aligned struct (a zero-length array of i128 gives it the alignment) starts at an
// even register: x1 is skipped after %a.
func @aligned(%a: i32, %s: struct<C>{array<0 x i128>, i64}, %b: i32) -> struct<C>{array<0 x i128>, i64} {
  %x: i64 = agg.extract %s, 1
  %a64: i64 = int.sext %a
  %b64: i64 = int.sext %b
  %y: i64 = int.add.wrap %x, %a64
  %z: i64 = int.add.wrap %y, %b64
  %e: array<0 x i128> = agg.extract %s, 0
  %r: struct<C>{array<0 x i128>, i64} = agg.make %e, %z
  func.ret %r
}

func @call_aligned(%x: i64) -> struct<C>{array<0 x i128>, i64} {
  %e: array<0 x i128> = agg.make @138:3
  %s: struct<C>{array<0 x i128>, i64} = agg.make %e, %x
  %a: i32 = int.const 10
  %b: i32 = int.const 200
  %r: struct<C>{array<0 x i128>, i64} = func.call @aligned(%a, %s, %b)
  func.ret %r
}

// Larger than 16 bytes: a pointer to a copy the caller makes. The callee may write its copy;
// the caller's value doesn't change.
func @big(%s: struct<C>{i64, i64, i64}, %t: array<5 x f64>, %u: struct<C>{i8, array<16 x i8>}) -> struct<C>{i64, f64, i8, i64, i64} {
  %s0: i64 = agg.extract %s, 0
  %s2: i64 = agg.extract %s, 2
  %t4: f64 = agg.extract %t, 4
  %u1: array<16 x i8> = agg.extract %u, 1
  %u15: i8 = agg.extract %u1, 15
  %r: struct<C>{i64, f64, i8, i64, i64} = agg.make %s2, %t4, %u15, %s0, %s2
  func.ret %r
}

func @bigs(%k: i64) -> struct<C>{i64, f64, i8, i64, i64} {
  %one: i64 = int.const 1
  %k1: i64 = int.add.wrap %k, %one
  %s: struct<C>{i64, i64, i64} = agg.make %k, %one, %k1
  %h: f64 = float.const 0.5
  %t: array<5 x f64> = agg.make %h, %h, %h, %h, %h
  %b: i8 = int.trunc.wrap %k
  %bs: array<16 x i8> = agg.make %b, %b, %b, %b, %b, %b, %b, %b, %b, %b, %b, %b, %b, %b, %b, %b
  %u: struct<C>{i8, array<16 x i8>} = agg.make %b, %bs
  %r: struct<C>{i64, f64, i8, i64, i64} = func.call @big(%s, %t, %u)
  func.ret %r
}

// A pointer inside a struct keeps its provenance: the callee loads through it.
func @deref(%s: struct<C>{i32, ptr}, %t: struct<C>{ptr, ptr, ptr}) -> i32 {
  %p: ptr = agg.extract %s, 1
  %x: i32 = mem.load %p, align 4
  %q: ptr = agg.extract %t, 2
  %y: i32 = mem.load %q, align 4
  %r: i32 = int.add.wrap %x, %y
  func.ret %r
}

func @pointers() -> i32 {
  %p: ptr = mem.stack.of i32, align 4
  %q: ptr = mem.stack.of i32, align 4
  %a: i32 = int.const 40
  %b: i32 = int.const 2
  mem.store i32 %a, %p, align 4
  mem.store i32 %b, %q, align 4
  %s: struct<C>{i32, ptr} = agg.make %b, %p
  %n: ptr = ptr.null
  %t: struct<C>{ptr, ptr, ptr} = agg.make %n, %p, %q
  %r: i32 = func.call @deref(%s, %t)
  func.ret %r
}

// Empty structs take nothing; struct<auto> and struct<packed> have their own layouts.
func @odd(%e: struct<C>{}, %a: struct<auto>{i8, i64, i16}, %p: struct<packed>{f32, f32}, %x: i32) -> struct<auto>{i8, i64, i16} {
  %a0: i8 = agg.extract %a, 0
  %a1: i64 = agg.extract %a, 1
  %x64: i64 = int.sext %x
  %b: i64 = int.add.wrap %a1, %x64
  %p1: f32 = agg.extract %p, 1
  %h: i16 = float.to_int.s.sat %p1
  %r: struct<auto>{i8, i64, i16} = agg.make %a0, %b, %h
  func.ret %r
}

func @odds(%x: i32) -> struct<auto>{i8, i64, i16} {
  %e: struct<C>{} = agg.make @208:3
  %c: i8 = int.const 9
  %l: i64 = int.const -5
  %s: i16 = int.const 7
  %a: struct<auto>{i8, i64, i16} = agg.make %c, %l, %s
  %f: f32 = float.const 6.5
  %p: struct<packed>{f32, f32} = agg.make %f, %f
  %r: struct<auto>{i8, i64, i16} = func.call @odd(%e, %a, %p, %x)
  func.ret %r
}

// To C: the arguments arrive as their values, and C's result comes back.
func @to_c(%x: i32) -> struct<C>{i32, f32} {
  %f: f32 = float.const 0.75
  %h: struct<C>{f32, f32, f32} = agg.make %f, %f, %f
  %c: i8 = int.const 3
  %s: struct<C>{i8, i32} = agg.make %c, %x
  %p: ptr = mem.stack.of i32, align 4
  %l: i64 = int.const 11
  %b: struct<C>{i64, ptr, i64} = agg.make %l, %p, %l
  %d: f64 = float.const 2.0
  %e: struct<C>{f64} = agg.make %d
  %r: struct<C>{i32, f32} = func.call @see(%h, %s, %b, %e)
  func.ret %r
}

// run: @hfa4_out() -> returned {f32 1.5, f32 0.125, f32 -2.25, f32 1.5}
// run: @hfa3_out() -> returned {f64 1e300, f64 1e300, f64 1e300}
// run: @smalls() -> returned {i64 8000000000, i32 1065453216, i16 293, i8 -14}
// run: @r3(5) -> returned {i8 5, i8 10, i8 5}
// run: @r12(-3) -> returned {i32 -3, f32 -3.0, i32 -3}
// run: @r16(null, 9) -> returned {ptr null, i64 9}
// run: @mixed2(1.5, -2.5) -> returned {f32 1.5, f64 -2.5}
// run: @call_aligned(1000) -> returned {{}, i64 1210}
// run: @bigs(6) -> returned {i64 7, f64 0.5, i8 6, i64 6, i64 7}
// run: @pointers() -> returned i32 42
// run: @odds(4) -> returned {i8 9, i64 -1, i16 6}
// run: @to_c(8) -> @see({f32 0.75, f32 0.75, f32 0.75}, {i8 3, i32 8}, {i64 11, ptr #1, i64 11}, {f64 2.0}) -> {i32 0, f32 0.0}; returned {i32 0, f32 0.0}
