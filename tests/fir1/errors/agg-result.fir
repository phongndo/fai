// Outside HFIR, aggregates are values only to cross calls: memory is accessed by scalars.
// error: in @f: @?: struct<C>{i32} can't be loaded: outside HFIR, memory is accessed by scalars
layer mfir
func @f(%p: ptr) {
  %x: struct<C>{i32} = mem.load %p, align 4
  func.ret
}
