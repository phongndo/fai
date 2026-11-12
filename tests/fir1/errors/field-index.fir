// ptr.field names a field that exists.
// error: in @f: @?: struct<C>{i32, i8} has no field 2
func @f(%p: ptr) -> ptr {
  %q: ptr = ptr.field.inbounds struct<C>{i32, i8} %p, 2
  func.ret %q
}
