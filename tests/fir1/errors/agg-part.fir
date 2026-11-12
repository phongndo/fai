// Struct fields need a size in whole bytes.
// error: in @f: @?: i1 can't be part of struct<C>{i32, i1}
func @f() -> i64 {
  %n: i64 = ty.size struct<C>{i32, i1}
  func.ret %n
}
