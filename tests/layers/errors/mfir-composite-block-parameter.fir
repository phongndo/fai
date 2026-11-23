// error: in @pass: @?: struct<C>{i32, i32} can't be the block parameter %s in layer mfir: outside HFIR only calls pass a struct or an array whole
// A block's parameters stay scalar outside HFIR.
layer mfir
func @pass(%a: struct<C>{i32, i32}) -> i32 {
  %r: i32 = cf.blocks {
  ^entry:
    cf.br ^done(%a)
  ^done(%s: struct<C>{i32, i32}):
    %x: i32 = agg.extract %s, 0
    cf.yield %x
  }
  func.ret %r
}
