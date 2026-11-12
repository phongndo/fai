// Checked arithmetic (decision: Checked arithmetic): `int.add.overflow.s` and friends give the
// wrapped result and whether the operation overflowed, exactly when `int.add.s.trap` would trap.
// Languages that trap on overflow use the `.s.trap` and `.u.trap` modifiers. HFIR lowers the
// pairs to `.wrap` arithmetic in a wider type and a comparison.

func @add_s(%a: i8, %b: i8) -> (i8, i1) {
  %r: i8, %o: i1 = int.add.overflow.s %a, %b @1:1
  func.ret %r, %o
}

func @add_u(%a: i8, %b: i8) -> (i8, i1) {
  %r: i8, %o: i1 = int.add.overflow.u %a, %b @2:1
  func.ret %r, %o
}

func @sub_s(%a: i8, %b: i8) -> (i8, i1) {
  %r: i8, %o: i1 = int.sub.overflow.s %a, %b @3:1
  func.ret %r, %o
}

func @sub_u(%a: i8, %b: i8) -> (i8, i1) {
  %r: i8, %o: i1 = int.sub.overflow.u %a, %b @4:1
  func.ret %r, %o
}

func @mul_s(%a: i8, %b: i8) -> (i8, i1) {
  %r: i8, %o: i1 = int.mul.overflow.s %a, %b @5:1
  func.ret %r, %o
}

func @mul_u(%a: i8, %b: i8) -> (i8, i1) {
  %r: i8, %o: i1 = int.mul.overflow.u %a, %b @6:1
  func.ret %r, %o
}

// Odd and wide widths, and i1.
func @odd(%a: i7, %b: i7) -> (i7, i1) {
  %r: i7, %o: i1 = int.mul.overflow.s %a, %b @7:1
  func.ret %r, %o
}

func @wide(%a: i65, %b: i65) -> (i65, i1) {
  %r: i65, %o: i1 = int.add.overflow.u %a, %b @8:1
  func.ret %r, %o
}

func @bit(%a: i1, %b: i1) -> (i1, i1) {
  %r: i1, %o: i1 = int.mul.overflow.s %a, %b @9:1
  func.ret %r, %o
}

// A Rust-style checked add: branch on the flag, trapping as `int.add.s.trap` would.
func @checked(%a: i32, %b: i32) -> i32 {
  %r: i32, %o: i1 = int.add.overflow.s %a, %b @10:1
  cf.if %o {
    %t: i32 = int.add.s.trap %a, %b @11:1
    cf.yield
  } else {
    cf.yield
  }
  func.ret %r
}

// Facts on the results are checked.
func @fact(%a: i8, %b: i8) -> i8 {
  %r: i8 [range.s(0, 100) assume], %o: i1 = int.add.overflow.s %a, %b @12:1
  func.ret %r
}

func @fact_flag(%a: i8, %b: i8) -> i8 {
  %r: i8, %o: i1 [range.u(0, 0) assume] = int.add.overflow.u %a, %b @13:1
  func.ret %r
}

// run: @add_s(100, 27) -> returned i8 127, i1 0
// run: @add_s(100, 28) -> returned i8 -128, i1 1
// run: @add_s(-128, -1) -> returned i8 127, i1 1
// run: @add_u(200, 55) -> returned i8 -1, i1 0
// run: @add_u(200, 56) -> returned i8 0, i1 1
// run: @sub_s(-128, 1) -> returned i8 127, i1 1
// run: @sub_s(0, -128) -> returned i8 -128, i1 1
// run: @sub_s(-1, -128) -> returned i8 127, i1 0
// run: @sub_u(3, 4) -> returned i8 -1, i1 1
// run: @sub_u(4, 4) -> returned i8 0, i1 0
// run: @mul_s(-128, -1) -> returned i8 -128, i1 1
// run: @mul_s(-16, 8) -> returned i8 -128, i1 0
// run: @mul_s(16, 8) -> returned i8 -128, i1 1
// run: @mul_u(16, 16) -> returned i8 0, i1 1
// run: @mul_u(15, 17) -> returned i8 -1, i1 0
// run: @odd(-8, 8) -> returned i7 -64, i1 0
// run: @odd(8, 8) -> returned i7 -64, i1 1
// run: @wide(36893488147419103231, 1) -> returned i65 0, i1 1
// run: @wide(18446744073709551616, 1) -> returned i65 -18446744073709551615, i1 0
// run: @bit(1, 1) -> returned i1 1, i1 1
// run: @bit(1, 0) -> returned i1 0, i1 0
// run: @add_s(poison, 1) -> returned i8 poison, i1 poison
// run: @mul_u(1, poison) -> returned i8 poison, i1 poison
// run: @checked(2147483647, 1) -> trap overflow @11:1
// run: @checked(1, 2) -> returned i32 3
// run: @fact(100, 1) -> ub fact @12:1 (%r breaks a fact)
// run: @fact(50, 1) -> returned i8 51
// run: @fact_flag(255, 1) -> ub fact @13:1 (%o breaks a fact)
