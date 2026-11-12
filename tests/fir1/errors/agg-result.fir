// An aggregate is not a value type.
// error: in @f: @?: struct<C>{i32} can't be loaded: it is not a value type
func @f(%p: ptr) {
  %x: struct<C>{i32} = mem.load %p, align 4
  func.ret
}
