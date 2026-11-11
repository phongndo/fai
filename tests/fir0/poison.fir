// How poison flows, and where it becomes UB.
// run: @flows(poison) -> returned i32 poison
// run: @flows(1) -> returned i32 2
// An op that can trap needs defined inputs.
// run: @trapping_add(poison) -> ub poison @1:1
// freeze turns poison into some value; the reference tool picks 0.
// run: @freeze(poison) -> returned i32 0
// run: @freeze(7) -> returned i32 7
// Branching on poison is UB.
// run: @branch(poison) -> ub poison @2:1
// run: @branch(1) -> returned i32 10
// run: @branch(0) -> returned i32 20
// run: @select(1, 3, 4) -> returned i32 3
// run: @select(poison, 3, 4) -> returned i32 poison
// run: @less(1, 2) -> returned i1 1
func @flows(%x: i32) -> i32 {
  %r: i32 = int.add.wrap %x, %x
  func.ret %r
}

func @trapping_add(%x: i32) -> i32 {
  %one: i32 = int.const 1
  %r: i32 = int.add.s.trap %x, %one @1:1
  func.ret %r
}

func @freeze(%x: i32) -> i32 {
  %r: i32 = freeze %x
  func.ret %r
}

func @branch(%c: i1) -> i32 {
  %r: i32 = cf.if %c @2:1 {
    %ten: i32 = int.const 10
    cf.yield %ten
  } else {
    %twenty: i32 = int.const 20
    cf.yield %twenty
  }
  func.ret %r
}

func @select(%c: i1, %a: i32, %b: i32) -> i32 {
  %r: i32 = select %c, %a, %b
  func.ret %r
}

func @less(%a: i32, %b: i32) -> i1 {
  %r: i1 = int.cmp.slt %a, %b
  func.ret %r
}
