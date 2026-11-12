// More composites than registers (decision: C ABI for aggregates): one that doesn't fit the
// registers left goes on the stack as its bytes, and closes its class's registers to the
// arguments after it (AAPCS64's C.3 and C.13); a 16-byte aligned one starts at an even register
// or a 16-byte aligned stack slot; one passed by reference is a pointer in a register or a slot.

// Seven x registers taken: a two-word struct goes on the stack, and so does the i64 after it,
// though x7 is free.
func @gp_spill(%a: i64, %b: i64, %c: i64, %d: i64, %e: i64, %f: i64, %g: i64, %s: struct<C>{i64, i32}, %h: i64) -> struct<C>{i64, i64} {
  %s0: i64 = agg.extract %s, 0
  %s1: i32 = agg.extract %s, 1
  %s164: i64 = int.sext %s1
  %x: i64 = int.add.wrap %a, %g
  %y: i64 = int.add.wrap %s0, %s164
  %z: i64 = int.add.wrap %y, %h
  %r: struct<C>{i64, i64} = agg.make %x, %z
  func.ret %r
}

// Six d registers taken: an HFA of three floats goes on the stack as its 12 bytes (rounded to
// 16), and so does the f32 after it.
func @fp_spill(%a: f64, %b: f64, %c: f64, %d: f64, %e: f64, %f: f64, %s: struct<C>{f32, f32, f32}, %x: f32, %y: struct<C>{f64, f64}) -> struct<C>{f32, f32, f64} {
  %s2: f32 = agg.extract %s, 2
  %y1: f64 = agg.extract %y, 1
  %t: f64 = float.add %f, %y1
  %r: struct<C>{f32, f32, f64} = agg.make %s2, %x, %t
  func.ret %r
}

// Nine two-word structs: four in x registers, the rest on the stack; a 16-byte aligned one on
// the stack starts at a 16-byte boundary; a large one is a pointer in a stack slot.
func @many(%p0: struct<C>{i64, i64}, %p1: struct<C>{i64, i64}, %p2: struct<C>{i64, i64}, %p3: struct<C>{i64, i64}, %p4: struct<C>{i64, i64}, %q: i32, %al: struct<C>{array<0 x i128>, i64}, %big: struct<C>{i64, i64, i64}, %p5: struct<C>{i8, array<3 x i16>}) -> i64 {
  %a: i64 = agg.extract %p0, 1
  %b: i64 = agg.extract %p3, 0
  %c: i64 = agg.extract %p4, 1
  %d: i64 = agg.extract %al, 1
  %e: i64 = agg.extract %big, 2
  %f: array<3 x i16> = agg.extract %p5, 1
  %g: i16 = agg.extract %f, 2
  %g64: i64 = int.sext %g
  %q64: i64 = int.sext %q
  %s1: i64 = int.add.wrap %a, %b
  %s2: i64 = int.add.wrap %s1, %c
  %s3: i64 = int.add.wrap %s2, %d
  %s4: i64 = int.add.wrap %s3, %e
  %s5: i64 = int.add.wrap %s4, %g64
  %s6: i64 = int.add.wrap %s5, %q64
  func.ret %s6
}

func @spills(%k: i64) -> (struct<C>{i64, i64}, struct<C>{f32, f32, f32, f64}, i64) {
  %one: i64 = int.const 1
  %two: i64 = int.const 2
  %t32: i32 = int.const -32
  %s: struct<C>{i64, i32} = agg.make %k, %t32
  %r: struct<C>{i64, i64} = func.call @gp_spill(%one, %two, %two, %two, %two, %two, %k, %s, %two)
  %h: f64 = float.const 0.5
  %f: f32 = float.const 1.25
  %g: f32 = float.const -3.0
  %hf: struct<C>{f32, f32, f32} = agg.make %f, %f, %g
  %dd: struct<C>{f64, f64} = agg.make %h, %h
  %u: struct<C>{f32, f32, f64} = func.call @fp_spill(%h, %h, %h, %h, %h, %h, %hf, %f, %dd)
  %u0: f32 = agg.extract %u, 0
  %u1: f32 = agg.extract %u, 1
  %u2: f64 = agg.extract %u, 2
  %v: struct<C>{f32, f32, f32, f64} = agg.make %u0, %u1, %u0, %u2
  %p0: struct<C>{i64, i64} = agg.make %k, %one
  %p1: struct<C>{i64, i64} = agg.make %two, %two
  %p4: struct<C>{i64, i64} = agg.make %two, %k
  %q: i32 = int.const 1000
  %e: array<0 x i128> = agg.make @69:3
  %al: struct<C>{array<0 x i128>, i64} = agg.make %e, %k
  %big: struct<C>{i64, i64, i64} = agg.make %one, %one, %k
  %w: i16 = int.const -9
  %ws: array<3 x i16> = agg.make %w, %w, %w
  %c: i8 = int.const 4
  %p5: struct<C>{i8, array<3 x i16>} = agg.make %c, %ws
  %m: i64 = func.call @many(%p0, %p1, %p1, %p1, %p4, %q, %al, %big, %p5)
  func.ret %r, %v, %m
}

func @spill_gp(%k: i64) -> struct<C>{i64, i64} {
  %r: struct<C>{i64, i64}, %v: struct<C>{f32, f32, f32, f64}, %m: i64 = func.call @spills(%k)
  func.ret %r
}

func @spill_fp(%k: i64) -> struct<C>{f32, f32, f32, f64} {
  %r: struct<C>{i64, i64}, %v: struct<C>{f32, f32, f32, f64}, %m: i64 = func.call @spills(%k)
  func.ret %v
}

func @spill_many(%k: i64) -> i64 {
  %r: struct<C>{i64, i64}, %v: struct<C>{f32, f32, f32, f64}, %m: i64 = func.call @spills(%k)
  func.ret %m
}

// Nested and indirect calls: a composite result passed on at once, through a pointer.
func @twice(%s: struct<C>{i32, f64}) -> struct<C>{i32, f64} {
  %a: i32 = agg.extract %s, 0
  %b: f64 = agg.extract %s, 1
  %a2: i32 = int.add.wrap %a, %a
  %b2: f64 = float.add %b, %b
  %r: struct<C>{i32, f64} = agg.make %a2, %b2
  func.ret %r
}

func @nested(%x: i32) -> struct<C>{i32, f64} {
  %f: f64 = float.const 0.75
  %s: struct<C>{i32, f64} = agg.make %x, %f
  %t: struct<C>{i32, f64} = func.call @twice(%s)
  %p: ptr = func.addr @twice
  %u: struct<C>{i32, f64} = func.call.indirect func<(struct<C>{i32, f64}) -> struct<C>{i32, f64}> %p(%t)
  %v: struct<C>{i32, f64} = func.call @twice(%u)
  func.ret %v
}

// run: @spill_gp(10) -> returned {i64 11, i64 -20}
// run: @spill_fp(10) -> returned {f32 -3.0, f32 1.25, f32 -3.0, f64 1.0}
// run: @spill_many(10) -> returned i64 1024
// run: @nested(3) -> returned {i32 24, f64 6.0}
