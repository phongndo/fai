// An aggregate is not a value type outside HFIR.
// error: in @f: @?: struct<C>{i32} can't be loaded: it is not a value type
layer mfir
func @f(%p: ptr) {
  %x: struct<C>{i32} = mem.load %p, align 4
  func.ret
}
