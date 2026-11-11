// One overflow (127 + 1 in i8) under each overflow behavior.
// run: @add_wrap(127) -> returned i8 -128
// run: @add_nsw(127) -> returned i8 poison
// run: @add_nuw(127) -> returned i8 -128
// run: @add_nuw(-1) -> returned i8 poison
// run: @add_trap(127) -> trap overflow @4:3
// run: @add_trap(5) -> returned i8 6
// run: @add_sat(127) -> returned i8 127
// run: @add_ub(127) -> ub overflow @6:3
// 255 + 1 clamps to 255, which prints as -1.
// run: @add_usat(-1) -> returned i8 -1
// run: @mul_sat(100) -> returned i8 127
// run: @mul_sat(-100) -> returned i8 -128
// run: @sub_usat(3) -> returned i8 0
func @add_wrap(%x: i8) -> i8 {
  %one: i8 = int.const 1
  %r: i8 = int.add.wrap %x, %one
  func.ret %r
}

func @add_nsw(%x: i8) -> i8 {
  %one: i8 = int.const 1
  %r: i8 = int.add.nsw %x, %one
  func.ret %r
}

func @add_nuw(%x: i8) -> i8 {
  %one: i8 = int.const 1
  %r: i8 = int.add.nuw %x, %one
  func.ret %r
}

func @add_trap(%x: i8) -> i8 {
  %one: i8 = int.const 1
  %r: i8 = int.add.s.trap %x, %one @4:3
  func.ret %r
}

func @add_sat(%x: i8) -> i8 {
  %one: i8 = int.const 1
  %r: i8 = int.add.s.sat %x, %one
  func.ret %r
}

func @add_ub(%x: i8) -> i8 {
  %one: i8 = int.const 1
  %r: i8 = int.add.s.ub %x, %one @6:3
  func.ret %r
}

func @add_usat(%x: i8) -> i8 {
  %one: i8 = int.const 1
  %r: i8 = int.add.u.sat %x, %one
  func.ret %r
}

func @mul_sat(%x: i8) -> i8 {
  %two: i8 = int.const 2
  %r: i8 = int.mul.s.sat %x, %two
  func.ret %r
}

func @sub_usat(%x: i8) -> i8 {
  %five: i8 = int.const 5
  %r: i8 = int.sub.u.sat %x, %five
  func.ret %r
}
