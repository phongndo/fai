// Slices (decision: Slices): a `slice` is a pointer and an address-sized length counting
// elements, laid out as `struct<C>{ptr, iA}`. `slice.get` and `slice.set` check the index
// (unsigned) against the length: out of bounds traps with reason `bounds` (`.trap`) or is UB
// (`.ub`), and a `poison` index or length is UB. HFIR lowers them to a comparison and
// `cf.check.bounds`, `ptr.offset.inbounds` by the index times the stride, and the access.

func @sum(%n: i64) -> i32 {
  %p: ptr = mem.stack.of array<4 x i32>, align 4 @1:1
  %s: slice = slice.make %p, %n @2:1
  %zero: i64 = int.const 0 @3:1
  %one: i64 = int.const 1 @4:1
  %z32: i32 = int.const 0 @5:1
  %len: i64 = slice.len %s @6:1
  // Fill element i with i * 10, then add them up.
  %t: i32 = cf.loop iter(%i: i64 = %zero, %acc: i32 = %z32) {
    %done: i1 = int.cmp.uge %i, %len @7:1
    cf.if %done {
      cf.break %acc
    } else {
      cf.yield
    }
    %i32: i32 = int.trunc.wrap %i @8:1
    %ten: i32 = int.const 10 @9:1
    %v: i32 = int.mul.wrap %i32, %ten @10:1
    slice.set.trap i32 %v, %s, %i, align 4 @11:1
    %w: i32 = slice.get.trap %s, %i, align 4 @12:1
    %acc2: i32 = int.add.wrap %acc, %w @13:1
    %i2: i64 = int.add.wrap %i, %one @14:1
    cf.continue %i2, %acc2
  }
  func.ret %t
}

func @get(%i: i64, %n: i64) -> i32 {
  %p: ptr = mem.stack.of array<4 x i32>, align 4 @15:1
  %s: slice = slice.make %p, %n @16:1
  %seven: i32 = int.const 7 @17:1
  %zero: i64 = int.const 0 @18:1
  slice.set.ub i32 %seven, %s, %zero, align 4 @19:1
  %v: i32 = slice.get.trap %s, %i, align 4 @20:1
  func.ret %v
}

func @get_ub(%i: i64) -> i32 {
  %p: ptr = mem.stack.of array<4 x i32>, align 4 @21:1
  %two: i64 = int.const 2 @22:1
  %s: slice = slice.make %p, %two @23:1
  %v: i32 = slice.get.ub %s, %i, align 4 @24:1
  func.ret %v
}

// Elements that are structs: the access is one per leaf.
func @points(%x: i16, %y: i32) -> struct<C>{i16, i32} {
  %p: ptr = mem.stack.of array<3 x struct<C>{i16, i32}>, align 4 @25:1
  %three: i64 = int.const 3 @26:1
  %s: slice = slice.make %p, %three @27:1
  %pt: struct<C>{i16, i32} = agg.make %x, %y @28:1
  %two: i64 = int.const 2 @29:1
  slice.set.trap struct<C>{i16, i32} %pt, %s, %two, align 4 @30:1
  %q: struct<C>{i16, i32} = slice.get.trap %s, %two, align 4 @31:1
  func.ret %q
}

// A slice in memory, and inside a struct value; its pointer and length come back out.
func @stored(%n: i64) -> i64 {
  %buf: ptr = mem.stack 8, align 8 @32:1
  %s: slice = slice.make %buf, %n @33:1
  %cell: ptr = mem.stack.of slice, align 1 @34:1
  mem.store slice %s, %cell, align 8 @35:1
  %t: slice = mem.load %cell, align 8 @36:1
  %b: i8 = int.trunc.wrap %n @37:1
  %pair: struct<C>{slice, i8} = agg.make %t, %b @37:1
  %u: slice = agg.extract %pair, 0 @38:1
  %len: i64 = slice.len %u @39:1
  %q: ptr = slice.ptr %u @40:1
  func.ret %len
}

func @layout() -> (i64, i64) {
  %size: i64 = ty.size slice @41:1
  %off: i64 = ty.offset struct<C>{i8, slice}, 1 @42:1
  func.ret %size, %off
}

// run: @sum(4) -> returned i32 60
// run: @sum(5) -> ub out-of-bounds @11:1 (offset 16, 4 bytes, allocation size 16)
// run: @get(0, 1) -> returned i32 7
// run: @get(1, 1) -> trap bounds @20:1
// run: @get(-1, 4) -> trap bounds @20:1
// run: @get(poison, 4) -> ub poison @20:1 (slice index or length is poison)
// run: @get(0, poison) -> ub poison @19:1 (slice index or length is poison)
// run: @get_ub(1) -> returned i32 poison
// run: @get_ub(2) -> ub bounds @24:1 (index 2, length 2)
// run: @points(5, -6) -> returned {i16 5, i32 -6}
// run: @stored(9) -> returned i64 9
// run: @layout() -> returned i64 16, i64 8
