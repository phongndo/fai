// error: 3:1: the module's layer is declared more than once
layer mfir
layer mfir

func @f() {
  func.ret
}
