// aarch64.code is a function's whole body.
// error: aarch64.code must be a function's whole body
layer lfir aarch64

func @f() {
  aarch64.code {
  ^entry:
    aarch64.code {
    ^inner:
      aarch64.ret
    }
  }
}
