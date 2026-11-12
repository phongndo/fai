// slice.get takes a slice and an address-sized index.
// error: @1:1: operands: expected (slice, i64) but got (slice, i32)
func @f(%s: slice, %i: i32) {
  %x: i8 = slice.get.trap %s, %i, align 1 @1:1
  func.ret
}
