// A target's ops are LFIR only.
// error: aarch64.ret is not allowed in layer mfir; it is allowed in lfir aarch64
layer mfir

func @f() {
  aarch64.ret
}
