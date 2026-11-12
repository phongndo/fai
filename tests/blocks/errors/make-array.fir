// agg.make of an array takes one value per element.
// error: @1:1: operands: expected 3 values of type i8 for array<3 x i8> but got (i8, i8)
func @f(%a: i8) {
  %s: array<3 x i8> = agg.make %a, %a @1:1
  func.ret
}
