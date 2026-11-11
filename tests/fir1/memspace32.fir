// A 32-bit memory space: addresses are i32.
// run: @addr() -> returned i32 4096
memspace default ptr 32 addr 32

func @addr() -> i32 {
  %p: ptr = mem.stack 4, align 4
  %a: i32 = ptr.addr %p
  func.ret %a
}
