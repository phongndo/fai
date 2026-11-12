// Signatures are checked before any body. Unions are values only in HFIR.
// error: in @f: @?: union<i8, i16> is not a value type
layer mfir
func @g() {
  %x: i0 = int.const 0
  func.ret
}

func @f(%s: union<i8, i16>) {
  func.ret
}
