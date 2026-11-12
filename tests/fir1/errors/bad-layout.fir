// Struct layouts are C, packed, or auto.
// error: 4:32: unknown struct layout 'rust'
func @f() -> i64 {
  %n: i64 = ty.size struct<rust>{i32}
  func.ret %n
}
