// Structs and arrays in memory: typed stack slots, field and element addresses, and copies.
// run: @point(3, 4) -> returned i32 25
// run: @sum(4) -> returned i32 6
// A field address is ptr.offset by the field's offset, so it follows the in-bounds rule.
// run: @field_oob() -> returned ptr poison, ptr #1+16
// Element addresses scale by the stride; in bounds means within [0, size] of the allocation.
// run: @index(1) -> returned ptr #1+8
// run: @index(5) -> returned ptr #1+40
// run: @index(6) -> returned ptr poison
// run: @index(-1) -> returned ptr poison
// The wrap form allows anything, and wraps the product to the address size.
// run: @index_wrap(-1) -> returned ptr #1-8
// run: @index_wrap(2305843009213693952) -> returned ptr #1
// In bounds also needs the product to fit a signed address, even when it wraps back in.
// run: @index_overflow() -> returned ptr poison
// A copy keeps pointers' provenance and padding's poison exactly.
// run: @copy() -> returned i32 7, i8 poison, i32 7
// Overlapping copies read everything first.
// run: @overlap() -> returned i32 1, i32 1, i32 2
// A copy needs both sides in bounds and aligned.
// run: @copy_oob() -> ub out-of-bounds @3:5 (offset 0, 12 bytes, allocation size 8)
// The slot is aligned to the type's alignment, or more if asked.
// run: @aligned() -> returned i64 4096, i64 8192
func @point(%x: i32, %y: i32) -> i32 {
  %p: ptr = mem.stack.of struct<C>{i32, i32}, align 1
  %fx: ptr = ptr.field.inbounds struct<C>{i32, i32} %p, 0
  %fy: ptr = ptr.field.inbounds struct<C>{i32, i32} %p, 1
  mem.store i32 %x, %fx, align 4
  mem.store i32 %y, %fy, align 4
  %a: i32 = mem.load %fx, align 4
  %b: i32 = mem.load %fy, align 4
  %a2: i32 = int.mul.nsw %a, %a
  %b2: i32 = int.mul.nsw %b, %b
  %r: i32 = int.add.nsw %a2, %b2
  func.ret %r
}

// Fill an array with 0, 1, 2, ... and add it up.
func @sum(%n: i64) -> i32 {
  %arr: ptr = mem.stack.of array<4 x i32>, align 1
  %zero: i64 = int.const 0
  %one: i64 = int.const 1
  cf.loop iter(%i: i64 = %zero) {
    %done: i1 = int.cmp.sge %i, %n
    cf.if %done {
      cf.break
    }
    %e: ptr = ptr.index.inbounds i32 %arr, %i
    %v: i32 = int.trunc.wrap %i
    mem.store i32 %v, %e, align 4
    %i2: i64 = int.add.nsw %i, %one
    cf.continue %i2
  }
  %z: i32 = int.const 0
  %s: i32 = cf.loop iter(%j: i64 = %zero, %acc: i32 = %z) {
    %end: i1 = int.cmp.sge %j, %n
    cf.if %end {
      cf.break %acc
    }
    %f: ptr = ptr.index.inbounds i32 %arr, %j
    %w: i32 = mem.load %f, align 4
    %acc2: i32 = int.add.nsw %acc, %w
    %j2: i64 = int.add.nsw %j, %one
    cf.continue %j2, %acc2
  }
  func.ret %s
}

func @field_oob() -> (ptr, ptr) {
  %p: ptr = mem.stack 8, align 8
  %f: ptr = ptr.field.inbounds struct<C>{i8, ptr, i16} %p, 2
  %g: ptr = ptr.field.wrap struct<C>{i8, ptr, ptr} %p, 2
  func.ret %f, %g
}

func @index(%i: i64) -> ptr {
  %p: ptr = mem.stack.of array<5 x i64>, align 1
  %e: ptr = ptr.index.inbounds i64 %p, %i
  func.ret %e
}

func @index_wrap(%i: i64) -> ptr {
  %p: ptr = mem.stack.of array<5 x i64>, align 1
  %e: ptr = ptr.index.wrap i64 %p, %i
  func.ret %e
}

func @index_overflow() -> ptr {
  %p: ptr = mem.stack.of array<5 x i64>, align 1
  %big: i64 = int.const 2305843009213693952
  %e: ptr = ptr.index.inbounds i64 %p, %big
  func.ret %e
}

// Copy a struct holding a pointer and padding, then read through the copy.
func @copy() -> (i32, i8, i32) {
  %x: ptr = mem.stack 4, align 4
  %seven: i32 = int.const 7
  mem.store i32 %seven, %x, align 4
  %a: ptr = mem.stack.of struct<C>{i8, ptr}, align 1
  %af: ptr = ptr.field.inbounds struct<C>{i8, ptr} %a, 1
  mem.store ptr %x, %af, align 8
  %b: ptr = mem.stack.of struct<C>{i8, ptr}, align 1
  mem.copy struct<C>{i8, ptr} %b, %a, align 8
  %bf: ptr = ptr.field.inbounds struct<C>{i8, ptr} %b, 1
  %q: ptr = mem.load %bf, align 8
  %v: i32 = mem.load %q, align 4
  %one: i64 = int.const 1
  %pad: ptr = ptr.offset.inbounds %b, %one
  %pv: i8 = mem.load %pad, align 1
  %w: i32 = mem.load %x, align 4
  func.ret %v, %pv, %w
}

func @overlap() -> (i32, i32, i32) {
  %arr: ptr = mem.stack.of array<3 x i32>, align 1
  %i0: i64 = int.const 0
  %i1: i64 = int.const 1
  %i2: i64 = int.const 2
  %e0: ptr = ptr.index.inbounds i32 %arr, %i0
  %e1: ptr = ptr.index.inbounds i32 %arr, %i1
  %e2: ptr = ptr.index.inbounds i32 %arr, %i2
  %one: i32 = int.const 1
  %two: i32 = int.const 2
  mem.store i32 %one, %e0, align 4
  mem.store i32 %two, %e1, align 4
  mem.copy array<2 x i32> %e1, %e0, align 4
  %a: i32 = mem.load %e0, align 4
  %b: i32 = mem.load %e1, align 4
  %c: i32 = mem.load %e2, align 4
  func.ret %a, %b, %c
}

func @copy_oob() {
  %a: ptr = mem.stack.of struct<C>{i32, i32, i32}, align 1 @1:5
  %b: ptr = mem.stack 8, align 4 @2:5
  mem.copy struct<C>{i32, i32, i32} %a, %b, align 4 @3:5
  func.ret
}

func @aligned() -> (i64, i64) {
  %a: ptr = mem.stack.of i8, align 1
  %b: ptr = mem.stack.of struct<C>{i8}, align 4096
  %x: i64 = ptr.addr %a
  %y: i64 = ptr.addr %b
  func.ret %x, %y
}
