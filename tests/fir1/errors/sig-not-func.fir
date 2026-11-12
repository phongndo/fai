// An indirect call needs a function type.
// error: in @f: @?: ptr is not a function type
func @f(%p: ptr) {
  func.call.indirect ptr %p()
  func.ret
}
