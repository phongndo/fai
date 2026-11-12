// error: in @f: @?: no block ^nope in the enclosing aarch64.code
layer lfir aarch64
func @f() {
  aarch64.code {
  ^entry:
    aarch64.b.exn ^nope, ^entry
  }
}
