// An external call exposes everything the callee can reach, since it may turn any pointer it holds
// into an integer: its pointer arguments, the pointers stored in memory it may read, and, through
// `exposed` and `globals`, more. Afterwards `ptr.from_exposed` can find those allocations.
// A pointer argument is exposed, even to a callee that touches no memory.
// run: @arg_exposed() -> @keep(ptr #2) -> (); returned i32 5
// Without the call, the address has no provenance.
// run: @not_exposed() -> ub no-provenance @3:3 (address 4096 belongs to no exposed allocation)
// A pointer stored in memory the callee may read is exposed too.
// run: @stored_read() -> @look(ptr #2) -> (); returned i32 7
// A callee that may not read its argument's memory doesn't see the pointer stored there (the
// address is just past the exposed slot).
// run: @stored_unread() -> @keep(ptr #2) -> (); ub out-of-bounds @7:3 (address 4104 is outside every allocation it may belong to)
// With `read(exposed)`, the callee follows pointers through everything it can reach.
// run: @chain() -> @deep(ptr #2) -> (); returned i32 9
// With only `read(args)`, it sees one level.
// run: @chain_args() -> @look(ptr #2) -> (); ub out-of-bounds @9:3 (address 4112 is outside every allocation it may belong to)
// With `globals`, the module's globals are exposed.
// run: @globals() -> @touch() -> (); returned i32 11
extern func @keep(ptr) effects[] assume
extern func @look(ptr) effects[read(args)] assume
extern func @deep(ptr) effects[read(exposed)] assume
extern func @touch() effects[read(globals), write(globals)] assume

global @g: i32 = 11

func @arg_exposed() -> i32 {
  %s: ptr = mem.stack 4, align 4
  %five: i32 = int.const 5
  mem.store i32 %five, %s, align 4
  func.call @keep(%s)
  %a: i64 = ptr.addr %s
  %q: ptr = ptr.from_exposed %a
  %v: i32 = mem.load %q, align 4
  func.ret %v
}

func @not_exposed() -> i32 {
  %s: ptr = mem.stack 4, align 4 @1:3
  %a: i64 = ptr.addr %s @2:3
  %q: ptr = ptr.from_exposed %a
  %v: i32 = mem.load %q, align 4 @3:3
  func.ret %v
}

func @stored_read() -> i32 {
  %slot: ptr = mem.stack 8, align 8
  %x: ptr = mem.stack 4, align 4
  %seven: i32 = int.const 7
  mem.store i32 %seven, %x, align 4
  mem.store ptr %x, %slot, align 8
  func.call @look(%slot)
  %a: i64 = ptr.addr %x
  %q: ptr = ptr.from_exposed %a
  %v: i32 = mem.load %q, align 4
  func.ret %v
}

func @stored_unread() -> i32 {
  %slot: ptr = mem.stack 8, align 8 @1:3
  %x: ptr = mem.stack 4, align 4 @2:3
  mem.store ptr %x, %slot, align 8 @3:3
  func.call @keep(%slot) @4:3
  %a: i64 = ptr.addr %x @5:3
  %q: ptr = ptr.from_exposed %a @6:3
  %v: i32 = mem.load %q, align 4 @7:3
  func.ret %v
}

func @chain() -> i32 {
  %p1: ptr = mem.stack 8, align 8
  %p2: ptr = mem.stack 8, align 8
  %x: ptr = mem.stack 4, align 4
  %nine: i32 = int.const 9
  mem.store i32 %nine, %x, align 4
  mem.store ptr %x, %p2, align 8
  mem.store ptr %p2, %p1, align 8
  func.call @deep(%p1)
  %a: i64 = ptr.addr %x
  %q: ptr = ptr.from_exposed %a
  %v: i32 = mem.load %q, align 4
  func.ret %v
}

func @chain_args() -> i32 {
  %p1: ptr = mem.stack 8, align 8 @1:3
  %p2: ptr = mem.stack 8, align 8 @2:3
  %x: ptr = mem.stack 4, align 4 @3:3
  mem.store ptr %x, %p2, align 8 @4:3
  mem.store ptr %p2, %p1, align 8 @5:3
  func.call @look(%p1) @6:3
  %a: i64 = ptr.addr %x @7:3
  %q: ptr = ptr.from_exposed %a @8:3
  %v: i32 = mem.load %q, align 4 @9:3
  func.ret %v
}

func @globals() -> i32 {
  func.call @touch()
  %p: ptr = mem.global @g
  %a: i64 = ptr.addr %p
  %q: ptr = ptr.from_exposed %a
  %v: i32 = mem.load %q, align 4
  func.ret %v
}
