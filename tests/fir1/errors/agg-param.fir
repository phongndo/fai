// Signatures are checked before any body.
// error: in @f: @?: array<2 x i8> is not a value type
func @g() {
  %x: i0 = int.const 0
  func.ret
}

func @f(%s: array<2 x i8>) {
  func.ret
}
