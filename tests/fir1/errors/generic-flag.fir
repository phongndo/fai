// error: expected true or false but found 'yes'
func @f() {
  "cf.loop"() {progress = yes} ({
    cf.break
  })
  func.ret
}
