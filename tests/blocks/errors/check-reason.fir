// cf.check names a trap reason.
// error: unknown op 'cf.check.nope'
func @f(%c: i1) {
  cf.check.nope %c @1:1
  func.ret
}
