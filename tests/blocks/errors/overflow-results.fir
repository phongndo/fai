// int.add.overflow.s gives the result and an i1.
// error: @1:1: results: expected (i8, i1) but got (i8, i8)
func @f(%a: i8) {
  %r: i8, %o: i8 = int.add.overflow.s %a, %a @1:1
  func.ret
}
