// Calls between FIR functions.
// run: @fact(5) -> returned i32 120
// run: @use_divmod(17, 5) -> returned i32 32
// Facts on parameters are checked on entry.
// run: @needs_ptr(null) -> ub fact (%p breaks a fact)
func @fact(%n: i32) -> i32 {
  %one: i32 = int.const 1
  %small: i1 = int.cmp.sle %n, %one
  cf.if %small {
    func.ret %one
  }
  %m: i32 = int.sub.nsw %n, %one
  %f: i32 = func.call @fact(%m)
  %r: i32 = int.mul.nsw %n, %f
  func.ret %r
}

func @divmod(%a: i32, %b: i32) -> (i32, i32) {
  %q: i32 = int.div.s.ub %a, %b
  %r: i32 = int.rem.s.ub %a, %b
  func.ret %q, %r
}

func @use_divmod(%a: i32, %b: i32) -> i32 {
  %q: i32, %r: i32 = func.call @divmod(%a, %b)
  %ten: i32 = int.const 10
  %t: i32 = int.mul.nsw %q, %ten
  %s: i32 = int.add.nsw %t, %r
  func.ret %s
}

func @needs_ptr(%p: ptr [nonnull check]) {
  func.ret
}
