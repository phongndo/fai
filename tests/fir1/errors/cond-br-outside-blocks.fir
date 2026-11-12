// error: in @f: @?: cf.cond_br outside cf.blocks
// A jump can't leave its function or reach past a call.
func @f(%c: i1) {
  cf.cond_br %c, ^a, ^b
}
