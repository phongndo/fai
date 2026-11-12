// error: in @f: @?: exn.throw: expected (ptr) but got (i32)
func @f(%a: i32) {
  exn.throw %a
}
