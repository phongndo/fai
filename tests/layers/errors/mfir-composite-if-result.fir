// error: in @pick: @?: struct<C>{i32, i32} can't be a result of cf.if in layer mfir: outside HFIR only calls pass a struct or an array whole
// Outside HFIR a struct or an array is a value only where calls pass it whole. The lowering
// yields the two fields from the cf.if; selection can't take a struct there.
layer mfir
func @pick(%c: i1, %a: struct<C>{i32, i32}, %b: struct<C>{i32, i32}) -> struct<C>{i32, i32} {
  %r: struct<C>{i32, i32} = cf.if %c {
    cf.yield %a
  } else {
    cf.yield %b
  }
  func.ret %r
}
