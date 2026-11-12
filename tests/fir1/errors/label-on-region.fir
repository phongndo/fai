// error: in @f: @?: only blocks of cf.blocks have labels
func @f(%c: i1) {
  "cf.if"(%c) (^a {
  }, {
  })
  func.ret
}
