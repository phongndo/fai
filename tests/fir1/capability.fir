// CHERI-style capabilities: pointers take 16 bytes, addresses are 64 bits.
// run: @fits(3) -> returned i32 3
// run: @too_small() -> ub out-of-bounds @1:3 (offset 0, 16 bytes, allocation size 8)
memspace default ptr 128 addr 64

func @fits(%v: i32) -> i32 {
  %x: ptr = mem.stack 4, align 4
  mem.store i32 %v, %x, align 4
  %slot: ptr = mem.stack 16, align 16
  mem.store ptr %x, %slot, align 16
  %p: ptr = mem.load %slot, align 16
  %r: i32 = mem.load %p, align 4
  func.ret %r
}

func @too_small() {
  %x: ptr = mem.stack 4, align 4
  %slot: ptr = mem.stack 8, align 8
  mem.store ptr %x, %slot, align 8 @1:3
  func.ret
}
