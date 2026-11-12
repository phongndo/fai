// error: the signature is variadic: write '...' after its 1 fixed arguments
func @f(%p: ptr) {
  %a: i32 = int.const 1
  func.call.indirect func<(i32, ...)> %p(%a, %a)
  func.ret
}
