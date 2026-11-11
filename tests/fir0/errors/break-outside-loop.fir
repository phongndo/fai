// error: cf.break outside a loop
func @f(%a: i32) -> i32 {
  cf.break %a
}
