// An access with align N is valid if the offset is a multiple of N and the allocation is aligned
// to at least N, or if the allocation already has an address and the byte's address is a multiple
// of N. The second case allows aligning by hand, like rounding malloc's result up to 32 for
// _mm256_load_ps. Here %p lands at 0x1010, and rounding gives 0x1020, offset 16.
// run: @manual(7) -> returned i32 7
// Without an address, only the allocation's alignment counts.
// run: @no_address() -> ub misaligned @1:3 (offset 0 in an allocation aligned to 16 with no address yet, access needs 32)
// With one, the address counts: 0x1010 isn't a multiple of 32.
// run: @unrounded() -> ub misaligned @1:3 (address 4112 is not a multiple of 32)
// The align fact uses the same rule as accesses.
// run: @fact_agrees() -> returned
func @manual(%x: i32) -> i32 {
  %pad: ptr = mem.stack 16, align 16
  %padaddr: i64 = ptr.addr %pad
  %n: i64 = int.const 64
  %p: ptr = mem.alloc.null c.malloc %n, align 16
  %a: i64 = ptr.addr %p
  %c31: i64 = int.const 31
  %up: i64 = int.add.wrap %a, %c31
  %mask: i64 = int.const -32
  %r: i64 = int.and %up, %mask
  %q: ptr [align(32) check] = ptr.with_addr %p, %r
  mem.store i32 %x, %q, align 32
  %y: i32 = mem.load %q, align 32
  mem.free c.malloc %p
  func.ret %y
}

func @no_address() -> i32 {
  %n: i64 = int.const 64
  %p: ptr = mem.alloc.null c.malloc %n, align 16
  %y: i32 = mem.load %p, align 32 @1:3
  mem.free c.malloc %p
  func.ret %y
}

func @unrounded() -> i32 {
  %pad: ptr = mem.stack 16, align 16
  %padaddr: i64 = ptr.addr %pad
  %n: i64 = int.const 64
  %p: ptr = mem.alloc.null c.malloc %n, align 16
  %a: i64 = ptr.addr %p
  %y: i32 = mem.load %p, align 32 @1:3
  mem.free c.malloc %p
  func.ret %y
}

func @fact_agrees() {
  %pad: ptr = mem.stack 16, align 16
  %padaddr: i64 = ptr.addr %pad
  %n: i64 = int.const 64
  %p: ptr = mem.alloc.null c.malloc %n, align 16
  %a: i64 = ptr.addr %p
  %sixteen: i64 = int.const 16
  %q: ptr [align(32) check] = ptr.offset.inbounds %p, %sixteen
  mem.free c.malloc %p
  func.ret
}
