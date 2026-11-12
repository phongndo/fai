// error: in @f: @?: a terminator must be the last op of its region
func @f(%p: ptr) {
  exn.throw %p
  func.ret
}
