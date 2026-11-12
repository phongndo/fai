// agg.extract takes an index of the type.
// error: @1:1: struct<C>{i32, ptr} has no part 2
func @f(%s: struct<C>{i32, ptr}) {
  %x: i32 = agg.extract %s, 2 @1:1
  func.ret
}
