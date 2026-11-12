// A branch names a block of the enclosing aarch64.code.
// error: no block ^nope in the enclosing aarch64.code
layer lfir aarch64

func @f() {
  aarch64.code {
  ^entry:
    aarch64.b ^nope
  }
}
