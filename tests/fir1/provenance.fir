// A pointer remembers which allocation it came from.
// Two adjacent allocations: one past the end of %a has the same address as the start of %b...
// run: @adjacent() -> returned i1 1
// ...but it still belongs to %a, so storing through it is out of bounds.
// run: @past_end() -> ub out-of-bounds @2:3 (offset 16, 4 bytes, allocation size 16)
// Comparing it with %b may go either way; the reference tool picks false.
// run: @cmp_end() -> returned i1 0
// run: @ordered() -> ub ptr-compare @1:3 (ordered comparison of pointers into different allocations)
// An exposed address can become a pointer again; one only read with ptr.addr can't.
// run: @exposed(5) -> returned i32 5
// run: @not_exposed() -> ub no-provenance @1:3 (address 4096 belongs to no exposed allocation)
// ptr.with_addr keeps the allocation.
// run: @with_addr(9) -> returned i32 9
// An address one past %a and at the start of %b may belong to either; each use picks the one
// that makes it valid.
// run: @either(1, 2) -> returned i32 3
func @adjacent() -> i1 {
  %a: ptr = mem.stack 16, align 16
  %b: ptr = mem.stack 16, align 16
  %n: i64 = int.const 16
  %end: ptr = ptr.offset.inbounds %a, %n
  %x: i64 = ptr.addr %end
  %y: i64 = ptr.addr %b
  %same: i1 = int.cmp.eq %x, %y
  func.ret %same
}

func @past_end() {
  %a: ptr = mem.stack 16, align 16
  %b: ptr = mem.stack 16, align 16
  %n: i64 = int.const 16
  %end: ptr = ptr.offset.inbounds %a, %n
  %one: i32 = int.const 1
  mem.store i32 %one, %end, align 4 @2:3
  func.ret
}

func @cmp_end() -> i1 {
  %a: ptr = mem.stack 16, align 16
  %b: ptr = mem.stack 16, align 16
  %n: i64 = int.const 16
  %end: ptr = ptr.offset.inbounds %a, %n
  %same: i1 = ptr.cmp.eq %end, %b
  func.ret %same
}

func @ordered() -> i1 {
  %a: ptr = mem.stack 16, align 16
  %b: ptr = mem.stack 16, align 16
  %lt: i1 = ptr.cmp.ult %a, %b @1:3
  func.ret %lt
}

func @exposed(%v: i32) -> i32 {
  %a: ptr = mem.stack 4, align 4
  %x: i64 = ptr.expose %a
  %p: ptr = ptr.from_exposed %x
  mem.store i32 %v, %p, align 4
  %r: i32 = mem.load %a, align 4
  func.ret %r
}

func @not_exposed() -> i32 {
  %a: ptr = mem.stack 4, align 4
  %x: i64 = ptr.addr %a
  %p: ptr = ptr.from_exposed %x
  %r: i32 = mem.load %p, align 4 @1:3
  func.ret %r
}

func @with_addr(%v: i32) -> i32 {
  %a: ptr = mem.stack 8, align 4
  %x: i64 = ptr.addr %a
  %four: i64 = int.const 4
  %y: i64 = int.add.wrap %x, %four
  %p: ptr = ptr.with_addr %a, %y
  mem.store i32 %v, %p, align 4
  %q: ptr = ptr.offset.inbounds %a, %four
  %r: i32 = mem.load %q, align 4
  func.ret %r
}

func @either(%x: i32, %y: i32) -> i32 {
  %a: ptr = mem.stack 16, align 16
  %b: ptr = mem.stack 16, align 16
  %ea: i64 = ptr.expose %a
  %eb: i64 = ptr.expose %b
  %sixteen: i64 = int.const 16
  %addr: i64 = int.add.wrap %ea, %sixteen
  %p: ptr = ptr.from_exposed %addr
  mem.store i32 %x, %p, align 4
  %minus4: i64 = int.const -4
  %q: ptr = ptr.offset.inbounds %p, %minus4
  mem.store i32 %y, %q, align 4
  %twelve: i64 = int.const 12
  %a12: ptr = ptr.offset.inbounds %a, %twelve
  %u: i32 = mem.load %b, align 4
  %v: i32 = mem.load %a12, align 4
  %r: i32 = int.add.wrap %u, %v
  func.ret %r
}
