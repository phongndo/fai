// cf.check takes an i1.
// error: @1:1: operands: expected (i1) but got (i8)
func @f(%c: i8) {
  cf.check.bounds %c @1:1
  func.ret
}
