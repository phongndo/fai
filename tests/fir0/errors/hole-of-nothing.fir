// error: in @f: @?: the hole ?h is of struct<C>{}, which holds nothing: a hole stands for at least one scalar
// A hole is lowered to a hole per scalar. One of a type without scalars would be lowered to
// nothing, and a program that stops at it in HFIR would run on in MFIR and return 7.
func @f() -> i32 {
  %s: struct<C>{} = copy ?h: struct<C>{}
  %x: i32 = int.const 7
  func.ret %x
}
