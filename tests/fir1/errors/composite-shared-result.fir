// Outside HFIR, a struct or array result is a function's only one, as C returns it.
// error: in @f: @?: struct<C>{i8} can't be one of several results: outside HFIR, a struct or array result is the only one
layer mfir
func @f(%a: struct<C>{i8}, %b: i32) -> (struct<C>{i8}, i32) {
  func.ret %a, %b
}
