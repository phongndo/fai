// The high half of a product is a 64-bit operation only.
// error: smulh and umulh are 64-bit only
layer lfir aarch64

func @f() {
  aarch64.code {
  ^entry:
    aarch64.smulh.w x0, x1, x2
    aarch64.ret
  }
}
