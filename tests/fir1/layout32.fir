// A 32-bit data layout like i386 System V: 4-byte pointers, and i64 aligned to 4.
// run: @sizes() -> returned i32 12, i32 4, i32 4, i32 4
// The integer table's rule: i128 isn't listed, so it takes the largest listed alignment.
// run: @wide() -> returned i32 4
memspace default ptr 32 addr 32 int 8:1 16:2 32:4 64:4

func @sizes() -> (i32, i32, i32, i32) {
  %s: i32 = ty.size struct<C>{i8, i64}
  %a: i32 = ty.align struct<C>{i8, i64}
  %o: i32 = ty.offset struct<C>{i8, i64}, 1
  %p: i32 = ty.align ptr
  func.ret %s, %a, %o, %p
}

func @wide() -> i32 {
  %a: i32 = ty.align i128
  func.ret %a
}
