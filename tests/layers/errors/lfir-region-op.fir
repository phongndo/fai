// The layer is checked before anything else about the op (here, its condition's type).
// error: in @f: @6:3: cf.if is not allowed in layer lfir aarch64; it is allowed in hfir, mfir
layer lfir aarch64

func @f(%c: i32) {
  cf.if %c @6:3 {
  }
  func.ret
}
