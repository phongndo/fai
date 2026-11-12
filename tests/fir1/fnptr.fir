// Function pointers: func.addr and func.call.indirect.
// run: @apply(3) -> returned i32 9
// The same function always has the same pointer; distinct functions compare unequal.
// run: @same() -> returned i1 1, i1 0
// A function is an allocation of size 0. Those an initializer names come right after the
// globals (@double is #2 and @square #3); the others are made when `func.addr` first names them.
// run: @alloc_id() -> returned ptr #4, ptr #1, ptr #5
// Through a table in a global, initialized with function addresses.
// run: @dispatch(0, 10) -> returned i32 20
// run: @dispatch(1, 10) -> returned i32 100
// A signature mismatch, a data pointer, a pointer into a function, null, and poison are UB.
// run: @wrong_sig() -> ub bad-call @2:3 (@square has type func<(i32) -> i32>)
// run: @not_func() -> ub bad-call @2:3 (#1 is not a function)
// run: @offset_fp() -> ub bad-call @3:3 (offset 1 is not the start of @square)
// run: @null_fp() -> ub no-provenance @2:3 (address 0 belongs to no exposed allocation)
// run: @poison_fp(poison) -> ub poison @1:3 (call through a poison pointer)
// No access reads or writes a function.
// run: @load_fp() -> ub func-access @2:3 (@square is a function)
// run: @store_fp() -> ub func-access @3:3 (@square is a function)
// run: @free_fp() -> ub bad-free @2:3 (@square is a function)
// Function addresses round-trip through integers once exposed.
// run: @exposed(5) -> returned i32 25, i64 4096
// Indirect recursion works like direct.
// run: @fact(5) -> returned i32 120
global const @table: array<2 x ptr> = {@double, @square}

func @square(%x: i32) -> i32 {
  %r: i32 = int.mul.wrap %x, %x
  func.ret %r
}

func @double(%x: i32) -> i32 {
  %r: i32 = int.add.wrap %x, %x
  func.ret %r
}

func @apply(%x: i32) -> i32 {
  %f: ptr = func.addr @square
  %r: i32 = func.call.indirect func<(i32) -> i32> %f(%x)
  func.ret %r
}

func @same() -> (i1, i1) {
  %a: ptr = func.addr @square
  %b: ptr = func.addr @square
  %c: ptr = func.addr @apply
  %eq: i1 = ptr.cmp.eq %a, %b
  %ne: i1 = ptr.cmp.eq %a, %c
  func.ret %eq, %ne
}

func @alloc_id() -> (ptr, ptr, ptr) {
  %f: ptr = func.addr @apply
  %t: ptr = mem.global @table
  %s: ptr = mem.stack 4, align 4
  func.ret %f, %t, %s
}

func @dispatch(%i: i64, %x: i32) -> i32 {
  %t: ptr = mem.global @table
  %e: ptr = ptr.index.inbounds ptr %t, %i
  %f: ptr = mem.load %e, align 8
  %r: i32 = func.call.indirect func<(i32) -> i32> %f(%x)
  func.ret %r
}

func @wrong_sig() -> i64 {
  %f: ptr = func.addr @square @1:3
  %r: i64 = func.call.indirect func<() -> i64> %f() @2:3
  func.ret %r
}

func @not_func() -> i32 {
  %t: ptr = mem.global @table @1:3
  %r: i32 = func.call.indirect func<() -> i32> %t() @2:3
  func.ret %r
}

func @offset_fp() -> i32 {
  %f: ptr = func.addr @square @1:3
  %one: i64 = int.const 1 @2:3
  %g: ptr = ptr.offset.wrap %f, %one
  %x: i32 = int.const 2
  %r: i32 = func.call.indirect func<(i32) -> i32> %g(%x) @3:3
  func.ret %r
}

func @null_fp() {
  %f: ptr = ptr.null @1:3
  func.call.indirect func<()> %f() @2:3
  func.ret
}

func @poison_fp(%f: ptr) {
  func.call.indirect func<()> %f() @1:3
  func.ret
}

func @load_fp() -> i8 {
  %f: ptr = func.addr @square @1:3
  %v: i8 = mem.load %f, align 1 @2:3
  func.ret %v
}

func @store_fp() {
  %f: ptr = func.addr @square @1:3
  %z: i8 = int.const 0 @2:3
  mem.store i8 %z, %f, align 1 @3:3
  func.ret
}

func @free_fp() {
  %f: ptr = func.addr @square @1:3
  mem.free c.malloc %f @2:3
  func.ret
}

func @exposed(%x: i32) -> (i32, i64) {
  %f: ptr = func.addr @square
  %a: i64 = ptr.expose %f
  %g: ptr = ptr.from_exposed %a
  %r: i32 = func.call.indirect func<(i32) -> i32> %g(%x)
  func.ret %r, %a
}

func @fact(%n: i32) -> i32 {
  %one: i32 = int.const 1
  %small: i1 = int.cmp.sle %n, %one
  cf.if %small {
    func.ret %one
  }
  %self: ptr = func.addr @fact
  %m: i32 = int.sub.nsw %n, %one
  %f: i32 = func.call.indirect func<(i32) -> i32> %self(%m)
  %r: i32 = int.mul.nsw %n, %f
  func.ret %r
}
