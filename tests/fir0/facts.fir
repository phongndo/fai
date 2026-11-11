// A fact is a claim about a value. Violating it is UB, whatever its trust tag.
// run: @percent(50) -> returned i32 50
// run: @percent(200) -> ub fact @1:3
// Facts constrain defined values only; poison passes.
// run: @percent(poison) -> returned i32 poison
// run: @small(3) -> returned i8 3
// run: @small(-1) -> ub fact @2:3
func @percent(%x: i32) -> i32 {
  %zero: i32 = int.const 0
  %p: i32 [range.s(0, 100) check] = int.add.wrap %x, %zero @1:3
  func.ret %p
}

func @small(%x: i8) -> i8 {
  %zero: i8 = int.const 0
  %y: i8 [range.u(0, 9) assume, range.s(-5, 5) proved] = int.or %x, %zero @2:3
  func.ret %y
}
