// error: in @f: @?: func.invoke names a handler outside cf.blocks
layer mfir
func @g() {
  func.ret
}
func @f() {
  func.invoke @g() unwind ^h
  func.ret
}
