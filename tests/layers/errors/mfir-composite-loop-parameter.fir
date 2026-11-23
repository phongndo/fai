// error: in @spin: @?: struct<C>{i32, i32} can't be the loop parameter %s in layer mfir: outside HFIR only calls pass a struct or an array whole
// The loop's result is a scalar here; its state is still a struct.
layer mfir
func @spin(%s0: struct<C>{i32, i32}) -> i32 {
  %r: i32 = cf.loop iter(%s: struct<C>{i32, i32} = %s0) {
    %x: i32 = agg.extract %s, 0
    cf.break %x
  }
  func.ret %r
}
