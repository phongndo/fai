// error: in @f: @?: every block of cf.blocks needs a label
func @f() {
  "cf.blocks"() {progress = false} ({
    "cf.yield"()
  })
  func.ret
}
