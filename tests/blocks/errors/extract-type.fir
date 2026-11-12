// agg.extract gives the part's type.
// error: @1:1: part 1 of array<2 x i8>: expected (i8) but got (i16)
func @f(%s: array<2 x i8>) {
  %x: i16 = agg.extract %s, 1 @1:1
  func.ret
}
