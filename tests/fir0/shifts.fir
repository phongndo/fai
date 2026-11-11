// Shifting an i8 by 9, which is at least the width, under each edge behavior.
// run: @shl_mask(1, 9) -> returned i8 2
// run: @shl_total(1, 9) -> returned i8 0
// run: @shr_s_total(-128, 9) -> returned i8 -1
// run: @shl_ub(1, 9) -> ub shift @1:1
// run: @shl_trap(1, 9) -> trap shift @2:1
// run: @shl_ub(1, 3) -> returned i8 8
// run: @shr_u_mask(-128, 7) -> returned i8 1
func @shl_mask(%x: i8, %n: i8) -> i8 {
  %r: i8 = int.shl.mask %x, %n
  func.ret %r
}

func @shl_total(%x: i8, %n: i8) -> i8 {
  %r: i8 = int.shl.total %x, %n
  func.ret %r
}

func @shr_s_total(%x: i8, %n: i8) -> i8 {
  %r: i8 = int.shr.s.total %x, %n
  func.ret %r
}

func @shl_ub(%x: i8, %n: i8) -> i8 {
  %r: i8 = int.shl.ub %x, %n @1:1
  func.ret %r
}

func @shl_trap(%x: i8, %n: i8) -> i8 {
  %r: i8 = int.shl.trap %x, %n @2:1
  func.ret %r
}

func @shr_u_mask(%x: i8, %n: i8) -> i8 {
  %r: i8 = int.shr.u.mask %x, %n
  func.ret %r
}
