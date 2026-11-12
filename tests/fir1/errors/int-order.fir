// Integer alignments are listed by increasing width.
// error: memspace: integer alignments must be listed by increasing width
memspace default ptr 64 addr 64 int 32:4 16:2

func @f() {
  func.ret
}
