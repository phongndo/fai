// poison gives scalars only.
// error: @1:1: struct<C>{i8} is not a scalar type
func @f() {
  %s: struct<C>{i8} = poison @1:1
  func.ret
}
