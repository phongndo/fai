// error: in @f: @?: cf.yield must end a cf.if or cf.try region or a block
func @f() {
  cf.yield
}
