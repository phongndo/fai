// error: @1:1: struct<auto>{i8, i32} can't be a variadic argument
func @f(%ap: ptr, ...) -> struct<auto>{i8, i32} {
  %v: struct<auto>{i8, i32} = va.arg %ap @1:1
  func.ret %v
}
