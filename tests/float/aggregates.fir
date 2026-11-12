// Floats in structs, arrays, unions, and slices, as values and in memory: the lowering passes
// them as scalars, and memory holds their bits.
global @g: struct<C>{f32, f64} = zero
global @h: array<2 x f64> = bytes "000000000000f83f000000000000f8ff"

// run: @pair(1.5, -2.25) -> returned f64 -0.75, {f32 1.5, f64 -0.75}
// run: @pair(nan(0x1), inf) -> returned f64 nan, {f32 nan(0x1), f64 nan}
// run: @arr(0.5) -> returned {f64 0.5, f64 0.0, f64 -0.5}
// run: @mem(3.0) -> returned {i8 1, f64 3.0, f32 3.0}, i64 4613937818241073152
// run: @mem(-nan(0x2)) -> returned {i8 1, f64 -nan(0x2), f32 nan}, i64 -4503599627370494
// run: @uni(0, 2.5) -> returned f64 2.5
// run: @uni(1, 2.5) -> returned f64 6.25
// run: @slice(1) -> returned f32 -3.5
// run: @slice(2) -> trap bounds
// run: @globals(7.0) -> returned {f32 7.0, f64 0.0}, {f64 1.5, f64 -nan}
// run: @loop(10) -> returned f64 0.9999999999999999, f32 1.0
func @make(%a: f32, %b: f64) -> struct<C>{f32, f64} {
  %s: struct<C>{f32, f64} = agg.make %a, %b
  func.ret %s
}

func @pair(%a: f32, %b: f64) -> (f64, struct<C>{f32, f64}) {
  %s: struct<C>{f32, f64} = func.call @make(%a, %b)
  %x: f32 = agg.extract %s, 0
  %y: f64 = agg.extract %s, 1
  %e: f64 = float.ext %x
  %r: f64 = float.add %e, %y
  %t: struct<C>{f32, f64} = agg.insert %s, %r, 1
  func.ret %r, %t
}

func @arr(%a: f64) -> array<3 x f64> {
  %z: f64 = float.const 0.0
  %n: f64 = float.neg %a
  %v: array<3 x f64> = agg.make %a, %z, %n
  func.ret %v
}

func @mem(%a: f64) -> (struct<packed>{i8, f64, f32}, i64) {
  %p: ptr = mem.stack.of struct<packed>{i8, f64, f32}, align 1
  %one: i8 = int.const 1
  %f: f32 = float.trunc %a
  %s: struct<packed>{i8, f64, f32} = agg.make %one, %a, %f
  mem.store struct<packed>{i8, f64, f32} %s, %p, align 1
  %r: struct<packed>{i8, f64, f32} = mem.load %p, align 1
  %q: ptr = ptr.field.inbounds struct<packed>{i8, f64, f32} %p, 1
  %bits: i64 = mem.load %q, align 1
  func.ret %r, %bits
}

func @uni(%which: i1, %x: f64) -> f64 {
  %u: union<f64, f32> = cf.if %which {
    %f: f32 = float.trunc %x
    %a: union<f64, f32> = union.make %f, 1
    cf.yield %a
  } else {
    %b: union<f64, f32> = union.make %x, 0
    cf.yield %b
  }
  %t: i32 = union.tag %u
  %zero: i32 = int.const 0
  %is0: i1 = int.cmp.eq %t, %zero
  %r: f64 = cf.if %is0 {
    %v: f64 = union.get.ub %u, 0
    cf.yield %v
  } else {
    %w: f32 = union.get.trap %u, 1
    %e: f64 = float.ext %w
    %m: f64 = float.mul %e, %e
    cf.yield %m
  }
  func.ret %r
}

func @slice(%i: i64) -> f32 {
  %p: ptr = mem.stack.of array<2 x f32>, align 4
  %a: f32 = float.const 1.25
  %b: f32 = float.const -3.5
  %v: array<2 x f32> = agg.make %a, %b
  mem.store array<2 x f32> %v, %p, align 4
  %two: i64 = int.const 2
  %s: slice = slice.make %p, %two
  %x: f32 = slice.get.trap %s, %i, align 4
  func.ret %x
}

func @globals(%x: f32) -> (struct<C>{f32, f64}, array<2 x f64>) {
  %p: ptr = mem.global @g
  mem.store f32 %x, %p, align 4
  %s: struct<C>{f32, f64} = mem.load %p, align 8
  %q: ptr = mem.global @h
  %a: array<2 x f64> = mem.load %q, align 8
  func.ret %s, %a
}

// Sum 0.1 n times: the rounding errors add up.
func @loop(%n: i32) -> (f64, f32) {
  %zero: i32 = int.const 0
  %z: f64 = float.const 0.0
  %tenth: f64 = float.const 0.1
  %r: f64 = cf.loop progress iter(%i: i32 = %zero, %acc: f64 = %z) {
    %done: i1 = int.cmp.sge %i, %n
    cf.if %done {
      cf.break %acc
    }
    %one: i32 = int.const 1
    %i2: i32 = int.add.nsw %i, %one
    %acc2: f64 = float.add %acc, %tenth
    cf.continue %i2, %acc2
  }
  %f: f32 = float.trunc %r
  func.ret %r, %f
}
