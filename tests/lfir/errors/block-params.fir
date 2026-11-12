// Values live in registers, so blocks of aarch64.code have no parameters.
// error: blocks of aarch64.code have no parameters
layer lfir aarch64

func @f() {
  aarch64.code {
  ^entry:
    aarch64.b ^next
  ^next(%x: i64):
    aarch64.ret
  }
}
