// error: this op takes two operands
// The generic form parses with any number of operands and regions; the verifier checks them.
// Printed, an op the readable form can't show stays in the generic form.
func @f(%a: i32) -> i32 {
  %s: i32 = "int.add.nsw"(%a) @4:3
  func.ret %s
}
