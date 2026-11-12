// Capability-style pointers: 16 bytes, aligned to 16, with 64-bit addresses.
// run: @f() -> returned i64 32, i64 16, i64 16
memspace default ptr 128 addr 64

func @f() -> (i64, i64, i64) {
  %s: i64 = ty.size struct<C>{i8, ptr}
  %a: i64 = ty.align ptr
  %o: i64 = ty.offset struct<C>{i8, ptr}, 1
  func.ret %s, %a, %o
}
