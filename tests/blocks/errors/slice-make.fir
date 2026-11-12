// slice.make takes a pointer and an address-sized length.
// error: @1:1: operands: expected (ptr, i32) but got (ptr, i64)
memspace default ptr 32 addr 32
func @f(%p: ptr, %n: i64) {
  %s: slice = slice.make %p, %n @1:1
  func.ret
}
