// agg.insert takes a value of the part's type.
// error: @1:1: part 0 of struct<C>{i32, ptr}: expected (i32) but got (ptr)
func @f(%s: struct<C>{i32, ptr}, %p: ptr) {
  %t: struct<C>{i32, ptr} = agg.insert %s, %p, 0 @1:1
  func.ret
}
