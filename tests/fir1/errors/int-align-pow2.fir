// Integer alignments are powers of two.
// error: memspace: alignment 3 of i32 must be a power of two
memspace default ptr 64 addr 64 int 8:1 32:3

func @f() {
  func.ret
}
