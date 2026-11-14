// Globals: allocations made before the call starts, numbered first, never freed.
// run: @read() -> returned i32 -5, i16 513, i8 104, ptr #3, i64 0
// A global keeps its contents across calls within one run.
// run: @twice() -> returned i32 2
// Padding is zero; a field initialized with zero is zero too.
// run: @padding() -> returned i8 0, i64 0
// A pointer initializer has the target's provenance: loads through it reach the target.
// run: @chain() -> returned i8 104
// Globals have addresses like other allocations, assigned when first observed.
// run: @address() -> returned i64 4096, i1 1
// Writing a const global is UB; writing a mutable one is fine.
// run: @write_const() -> ub const-write @2:3 (write to a const global)
// run: @write_mut() -> returned i32 9
// A copy into a const global writes it too.
// run: @copy_into_const() -> ub const-write @2:3 (write to a const global)
// Globals are never freed.
// run: @free_global() -> ub bad-free @2:3 (@counter is a global)
// run: @bytes() -> returned b32 (0x1, 0x2, 0x3, 0x4)
// A pointer initializer may point inside its target (C's `&table[1]`), with its provenance.
// run: @offset_init() -> returned i8 105, i16 513
// An integer initializing a pointer is an address with no provenance (C's `(void *)4096`).
// run: @int_ptr_init() -> returned i64 4096, i1 0
global @counter: i32 = 0
global @s: struct<C>{i32, i16, i8} = {-5, 513, zero}
global const @msg: array<3 x i8> = bytes "686900"
global @p: ptr = @msg
global @padded: struct<C>{i8, i64} align 16 = {zero, 0}
global @raw: b32 = 67305985
global @mid: ptr = offset(@msg, 1)
global @half: ptr = offset(@s, 4)
global @np: ptr = 4096

func @read() -> (i32, i16, i8, ptr, i64) {
  %s: ptr = mem.global @s
  %a: i32 = mem.load %s, align 4
  %f1: ptr = ptr.field.inbounds struct<C>{i32, i16, i8} %s, 1
  %b: i16 = mem.load %f1, align 2
  %m: ptr = mem.global @msg
  %c: i8 = mem.load %m, align 1
  %pp: ptr = mem.global @p
  %q: ptr = mem.load %pp, align 8
  %f2: ptr = ptr.field.inbounds struct<C>{i32, i16, i8} %s, 2
  %z: i8 = mem.load %f2, align 1
  %zz: i64 = int.zext %z
  func.ret %a, %b, %c, %q, %zz
}

func @bump() -> i32 {
  %g: ptr = mem.global @counter
  %v: i32 = mem.load %g, align 4
  %one: i32 = int.const 1
  %w: i32 = int.add.nsw %v, %one
  mem.store i32 %w, %g, align 4
  func.ret %w
}

func @twice() -> i32 {
  %a: i32 = func.call @bump()
  %b: i32 = func.call @bump()
  func.ret %b
}

func @padding() -> (i8, i64) {
  %g: ptr = mem.global @padded
  %one: i64 = int.const 1
  %pad: ptr = ptr.offset.inbounds %g, %one
  %a: i8 = mem.load %pad, align 1
  %f: ptr = ptr.field.inbounds struct<C>{i8, i64} %g, 1
  %b: i64 = mem.load %f, align 8
  func.ret %a, %b
}

func @chain() -> i8 {
  %pp: ptr = mem.global @p
  %q: ptr = mem.load %pp, align 8
  %c: i8 = mem.load %q, align 1
  func.ret %c
}

func @address() -> (i64, i1) {
  %g: ptr = mem.global @padded
  %a: i64 = ptr.addr %g
  %c: ptr = mem.global @counter
  %b: i64 = ptr.addr %c
  %ne: i1 = int.cmp.ne %a, %b
  func.ret %a, %ne
}

func @write_const() {
  %m: ptr = mem.global @msg @1:3
  %z: i8 = int.const 0
  mem.store i8 %z, %m, align 1 @2:3
  func.ret
}

func @write_mut() -> i32 {
  %g: ptr = mem.global @counter
  %nine: i32 = int.const 9
  mem.store i32 %nine, %g, align 4
  %v: i32 = mem.load %g, align 4
  func.ret %v
}

func @copy_into_const() {
  %src: ptr = mem.stack.of array<3 x i8>, align 1 @1:3
  %m: ptr = mem.global @msg
  mem.copy array<3 x i8> %m, %src, align 1 @2:3
  func.ret
}

func @free_global() {
  %g: ptr = mem.global @counter @1:3
  mem.free c.malloc %g @2:3
  func.ret
}

func @bytes() -> b32 {
  %g: ptr = mem.global @raw
  %v: b32 = mem.load %g, align 4
  func.ret %v
}

func @offset_init() -> (i8, i16) {
  %pp: ptr = mem.global @mid
  %q: ptr = mem.load %pp, align 8
  %c: i8 = mem.load %q, align 1
  %hp: ptr = mem.global @half
  %h: ptr = mem.load %hp, align 8
  %v: i16 = mem.load %h, align 2
  func.ret %c, %v
}

func @int_ptr_init() -> (i64, i1) {
  %pp: ptr = mem.global @np
  %q: ptr = mem.load %pp, align 8
  %a: i64 = ptr.addr %q
  %n: ptr = ptr.null
  %e: i1 = ptr.cmp.eq %q, %n
  func.ret %a, %e
}
