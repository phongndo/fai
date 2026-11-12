// An instruction belongs in a block of aarch64.code, not directly in a function's body.
// error: aarch64.mov.x must be inside a block of a target's code
layer lfir aarch64

func @f() {
  aarch64.mov.x x0, x1
  func.ret
}
