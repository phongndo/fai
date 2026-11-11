// error: noalias and readonly apply only to pointer parameters of functions
func @f() {
  %q: ptr [noalias assume] = ptr.null
  func.ret
}
