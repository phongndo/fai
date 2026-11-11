// error: the function body must end with func.ret
func @f(%a: i32) -> i32 {
  %b: i32 = int.const 1
}
