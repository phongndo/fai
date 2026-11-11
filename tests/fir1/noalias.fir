// noalias: for the call, a byte reached through %p and written by anyone may only be reached
// through %p (or pointers derived from it).
// run: @distinct() -> returned i32 0
// run: @same() -> ub noalias @1:3 (byte 0 of #1 is accessed both through a noalias parameter and another pointer, and written)
// Reads may be shared.
// run: @shared_reads() -> returned i32 4
// Pointers derived from %p are fine.
// run: @derived() -> returned i32 1
// readonly forbids writes through the parameter.
// run: @write_readonly() -> ub readonly @2:3 (write through a pointer derived from a readonly parameter)
func @write_then_read(%p: ptr [noalias assume], %q: ptr) -> i32 {
  %one: i32 = int.const 1
  mem.store i32 %one, %p, align 4
  %r: i32 = mem.load %q, align 4 @1:3
  func.ret %r
}

func @distinct() -> i32 {
  %a: ptr = mem.stack 4, align 4
  %b: ptr = mem.stack 4, align 4
  %zero: i32 = int.const 0
  mem.store i32 %zero, %b, align 4
  %r: i32 = func.call @write_then_read(%a, %b)
  func.ret %r
}

func @same() -> i32 {
  %a: ptr = mem.stack 4, align 4
  %zero: i32 = int.const 0
  mem.store i32 %zero, %a, align 4
  %r: i32 = func.call @write_then_read(%a, %a)
  func.ret %r
}

func @read_both(%p: ptr [noalias assume], %q: ptr) -> i32 {
  %x: i32 = mem.load %p, align 4
  %y: i32 = mem.load %q, align 4
  %r: i32 = int.add.wrap %x, %y
  func.ret %r
}

func @shared_reads() -> i32 {
  %a: ptr = mem.stack 4, align 4
  %two: i32 = int.const 2
  mem.store i32 %two, %a, align 4
  %r: i32 = func.call @read_both(%a, %a)
  func.ret %r
}

func @through_derived(%p: ptr [noalias assume]) -> i32 {
  %four: i64 = int.const 4
  %minus4: i64 = int.const -4
  %q: ptr = ptr.offset.inbounds %p, %four
  %r: ptr = ptr.offset.inbounds %q, %minus4
  %one: i32 = int.const 1
  mem.store i32 %one, %p, align 4
  %x: i32 = mem.load %r, align 4
  func.ret %x
}

func @derived() -> i32 {
  %a: ptr = mem.stack 8, align 4
  %r: i32 = func.call @through_derived(%a)
  func.ret %r
}

func @ro(%p: ptr [readonly assume]) {
  %one: i32 = int.const 1
  mem.store i32 %one, %p, align 4 @2:3
  func.ret
}

func @write_readonly() {
  %a: ptr = mem.stack 4, align 4
  func.call @ro(%a)
  func.ret
}
