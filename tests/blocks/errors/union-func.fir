// A function type is not a variant.
// error: func<()> can't be a variant of union<func<()>>
func @f(%u: union<func<()>>) {
  func.ret
}
