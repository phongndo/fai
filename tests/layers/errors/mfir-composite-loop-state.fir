// error: in @spin: @?: struct<C>{i32, i32} can't be a result of cf.loop in layer mfir: outside HFIR only calls pass a struct or an array whole
// A loop's state and its results stay scalar outside HFIR.
layer mfir
func @spin(%s0: struct<C>{i32, i32}) -> struct<C>{i32, i32} {
  %r: struct<C>{i32, i32} = cf.loop iter(%s: struct<C>{i32, i32} = %s0) {
    cf.break %s
  }
  func.ret %r
}
