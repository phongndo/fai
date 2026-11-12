// union.tag takes a union.
// error: @1:1: struct<C>{i32} is not a union
func @f(%s: struct<C>{i32}) {
  %t: i32 = union.tag %s @1:1
  func.ret
}
