// The generic form of cf.blocks and its branches: regions start with their labels, and a branch
// target is its label and argument count, its arguments being among the operands.
// run: @f(1) -> returned i32 1
// run: @f(2) -> returned i32 4
// run: @f(3) -> returned i32 1
// run: @f(4) -> returned i32 4
func @f(%x: i32) -> i32 {
  %one: i32 = int.const 1
  %r: i32 = "cf.blocks"() {progress = false} @2:3 (^entry {
    %c: i1 = "int.cmp.eq"(%x, %one)
    "cf.cond_br"(%c, %x, %x, %one) {f = ^sw(2), t = ^out(1)}
  }, ^sw(%v: i32, %w: i32) {
    "cf.switch"(%v, %w, %v, %v) {dflt = ^out(1), cases = [2: ^twice(1), 4: ^out(1)]}
  }, ^twice(%t: i32) {
    %d: i32 = "int.add.nsw"(%t, %t)
    "cf.br"(%d) {dest = ^out(1)}
  }, ^out(%o: i32) {
    "cf.yield"(%o)
  })
  "func.ret"(%r)
}
