// Registers are x0…x30, sp, xzr, and virtual registers v0, v1, ….
// error: expected a register like x0 or v1 but found 'x31'
layer lfir aarch64

func @f() {
  aarch64.code {
  ^entry:
    aarch64.mov.x x31, x1
    aarch64.ret
  }
}
