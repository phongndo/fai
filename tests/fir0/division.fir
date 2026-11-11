// Division as C, Java, Wasm, and a total (never-failing) language define it.
// run: @c_div(7, 2) -> returned i8 3
// run: @c_div(-7, 2) -> returned i8 -3
// run: @c_div(1, 0) -> ub div0 @1:1
// run: @c_div(-128, -1) -> ub overflow @1:1
// run: @c_rem(-7, 2) -> returned i8 -1
// Java: a zero divisor throws, MIN / -1 wraps, MIN % -1 is 0.
// run: @java_div(1, 0) -> trap div0 @2:1
// run: @java_div(-128, -1) -> returned i8 -128
// run: @java_rem(-128, -1) -> returned i8 0
// Wasm: both edge cases trap.
// run: @wasm_div(-128, -1) -> trap overflow @3:1
// run: @total_div(5, 0) -> returned i8 0
// run: @total_rem(5, 0) -> returned i8 5
// 200 is -56 as a signed i8, but unsigned division sees 200.
// run: @udiv(200, 3) -> returned i8 66
// run: @divmod(7, 3) -> returned i8 2, i8 1
func @c_div(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.div.s.ub %a, %b @1:1
  func.ret %r
}

func @c_rem(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.rem.s.ub %a, %b
  func.ret %r
}

func @java_div(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.div.s.trap.wrap %a, %b @2:1
  func.ret %r
}

func @java_rem(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.rem.s.trap.wrap %a, %b
  func.ret %r
}

func @wasm_div(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.div.s.trap %a, %b @3:1
  func.ret %r
}

func @total_div(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.div.s.total %a, %b
  func.ret %r
}

func @total_rem(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.rem.u.total %a, %b
  func.ret %r
}

func @udiv(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.div.u.ub %a, %b
  func.ret %r
}

func @divmod(%a: i8, %b: i8) -> (i8, i8) {
  %q: i8 = int.div.s.ub %a, %b
  %r: i8 = int.rem.s.ub %a, %b
  func.ret %q, %r
}
