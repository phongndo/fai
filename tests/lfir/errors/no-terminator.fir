// Every block ends with a branch, aarch64.ret, or aarch64.trap: there is no fall-through.
// error: a block must end with a terminator
layer lfir aarch64

func @f() {
  aarch64.code {
  ^entry:
    aarch64.mov.x x0, x1
  ^next:
    aarch64.ret
  }
}
