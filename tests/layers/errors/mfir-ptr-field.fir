// error: in @f: @6:3: ptr.field.inbounds is not allowed in layer mfir; it is allowed in hfir
layer mfir

func @f() -> ptr {
  %p: ptr = mem.stack.of struct<C>{i8, i32}, align 1
  %q: ptr = ptr.field.inbounds struct<C>{i8, i32} %p, 1 @6:3
  func.ret %q
}
