// The pointer alignment is a power of two.
// error: memspace: pointer alignment 6 must be a power of two
memspace default ptr 64 addr 64 align 6

func @f() {
  func.ret
}
