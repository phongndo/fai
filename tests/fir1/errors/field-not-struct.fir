// ptr.field needs a struct.
// error: in @f: @?: array<4 x i32> is not a struct
func @f(%p: ptr) -> ptr {
  %q: ptr = ptr.field.inbounds array<4 x i32> %p, 0
  func.ret %q
}
