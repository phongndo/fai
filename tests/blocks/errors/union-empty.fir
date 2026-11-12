// A union has at least one variant.
// error: union<> needs at least one variant
func @f(%u: union<>) {
  func.ret
}
