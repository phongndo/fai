// A function that observes an address it doesn't use, next to arithmetic that doesn't depend
// on it. The AArch64 differential test may excuse only the tokens that move with the address
// layout (the address itself), never the product: a miscompiled multiplication here must fail
// even though the module observes an address. (The previous rule excused every integer
// difference in a module that observes addresses.)
// run: @f(3) -> returned i64 4096, i64 21
// run: @f(-5) -> returned i64 4096, i64 -35
// run: @g(6) -> returned i64 42

func @f(%x: i64) -> (i64, i64) {
  %p: ptr = mem.stack 8, align 8
  %a: i64 = ptr.addr %p
  %k: i64 = int.const 7
  %y: i64 = int.mul.wrap %x, %k
  func.ret %a, %y
}

func @g(%x: i64) -> i64 {
  %k: i64 = int.const 7
  %y: i64 = int.mul.wrap %x, %k
  func.ret %y
}
