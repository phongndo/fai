// Stack memory: values round-trip, fresh memory is poison, and every access is checked.
// run: @roundtrip(42) -> returned i32 42
// run: @uninit() -> returned i32 poison
// run: @out_of_bounds() -> ub out-of-bounds @3:3 (offset 4, 8 bytes, allocation size 8)
// run: @misaligned() -> ub misaligned @3:3 (offset 2 in an allocation aligned to 4 with no address yet, access needs 4)
// A callee's stack memory ends when it returns.
// run: @dangling() -> ub use-after-free @2:3 (stack memory from @1:3, whose region has ended)
func @roundtrip(%x: i32) -> i32 {
  %p: ptr = mem.stack 4, align 4
  mem.store i32 %x, %p, align 4
  %y: i32 = mem.load %p, align 4
  func.ret %y
}

func @uninit() -> i32 {
  %p: ptr = mem.stack 4, align 4
  %y: i32 = mem.load %p, align 4
  func.ret %y
}

func @out_of_bounds() -> i64 {
  %p: ptr = mem.stack 8, align 4
  %four: i64 = int.const 4
  %q: ptr = ptr.offset.wrap %p, %four
  %y: i64 = mem.load %q, align 4 @3:3
  func.ret %y
}

func @misaligned() -> i32 {
  %p: ptr = mem.stack 8, align 4
  %two: i64 = int.const 2
  %q: ptr = ptr.offset.inbounds %p, %two
  %y: i32 = mem.load %q, align 4 @3:3
  func.ret %y
}

func @make() -> ptr {
  %p: ptr = mem.stack 4, align 4 @1:3
  func.ret %p
}

func @dangling() -> i32 {
  %p: ptr = func.call @make()
  %y: i32 = mem.load %p, align 4 @2:3
  func.ret %y
}
