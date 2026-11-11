// What memory holds: bits, poison, and pointer fragments.
// Copying a pointer byte by byte as b8 keeps its provenance.
// run: @copy_bytes(11) -> returned i32 11
// Copying it as integers works too, but exposes the pointer.
// run: @copy_ints(12) -> returned i32 12
// Integers are stored little-endian.
// run: @pun(16909060) -> returned b32 (0x4, 0x3, 0x2, 0x1)
// One unwritten byte makes the whole integer poison.
// run: @partial() -> returned i32 poison
func @copy_bytes(%v: i32) -> i32 {
  %x: ptr = mem.stack 4, align 4
  mem.store i32 %v, %x, align 4
  %src: ptr = mem.stack 8, align 8
  %dst: ptr = mem.stack 8, align 8
  mem.store ptr %x, %src, align 8
  %zero: i64 = int.const 0
  %one: i64 = int.const 1
  %eight: i64 = int.const 8
  cf.loop iter(%i: i64 = %zero) {
    %done: i1 = int.cmp.eq %i, %eight
    cf.if %done {
      cf.break
    }
    %s: ptr = ptr.offset.inbounds %src, %i
    %d: ptr = ptr.offset.inbounds %dst, %i
    %byte: b8 = mem.load %s, align 1
    mem.store b8 %byte, %d, align 1
    %next: i64 = int.add.nuw %i, %one
    cf.continue %next
  }
  %p: ptr = mem.load %dst, align 8
  %r: i32 = mem.load %p, align 4
  func.ret %r
}

func @copy_ints(%v: i32) -> i32 {
  %x: ptr = mem.stack 4, align 4
  mem.store i32 %v, %x, align 4
  %src: ptr = mem.stack 8, align 8
  %dst: ptr = mem.stack 8, align 8
  mem.store ptr %x, %src, align 8
  %bits: i64 = mem.load %src, align 8
  mem.store i64 %bits, %dst, align 8
  %p: ptr = mem.load %dst, align 8
  %r: i32 = mem.load %p, align 4
  func.ret %r
}

func @pun(%v: i32) -> b32 {
  %x: ptr = mem.stack 4, align 4
  mem.store i32 %v, %x, align 4
  %b: b32 = mem.load %x, align 4
  func.ret %b
}

func @partial() -> i32 {
  %x: ptr = mem.stack 4, align 4
  %one: i8 = int.const 1
  mem.store i8 %one, %x, align 1
  %r: i32 = mem.load %x, align 4
  func.ret %r
}
