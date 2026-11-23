// error: in @later: @?: struct<C>{i32, i32} can't be the hole ?h in layer mfir: outside HFIR only calls pass a struct or an array whole
// A hole of a struct is HFIR's: the lowering makes it a hole per field.
layer mfir
func @later() -> i32 {
  %s: struct<C>{i32, i32} = copy ?h: struct<C>{i32, i32}
  %x: i32 = agg.extract %s, 0
  func.ret %x
}
