// error: in @f: @?: cf.yield must end a cf.if region or a block
func @f() {
  cf.yield
}
