// Unions have no size.
// error: @1:1: union<i8> has no size in memory
func @f() {
  %n: i64 = ty.size union<i8> @1:1
  func.ret
}
