// error: memspace: pointer size 32 and address size 64
memspace default ptr 32 addr 64

func @f() {
  func.ret
}
