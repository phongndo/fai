// error: in @f: @?: array<2 x i8> can't be stored: outside HFIR, memory is accessed by scalars
layer mfir
func @f(%p: ptr, %s: array<2 x i8>) {
  mem.store array<2 x i8> %s, %p, align 1
  func.ret
}
