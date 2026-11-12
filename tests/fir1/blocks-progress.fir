// Jumps that never leave a `cf.blocks progress` are UB, like a `cf.loop progress` that never
// exits; without `progress`, the program just runs forever. The reference tool stops after its
// step budget.
// run: @spin_progress() -> out of fuel after 1000000 steps in a progress loop
// run: @spin() -> out of fuel after 1000000 steps
// run: @leaves(3) -> returned i32 0
func @spin_progress() {
  cf.blocks progress {
  ^a:
    cf.br ^b
  ^b:
    cf.br ^a
  }
  func.ret
}

func @spin() {
  cf.blocks {
  ^a:
    cf.br ^a
  }
  func.ret
}

func @leaves(%n: i32) -> i32 {
  %one: i32 = int.const 1
  %zero: i32 = int.const 0
  %r: i32 = cf.blocks progress {
  ^entry:
    cf.br ^loop(%n)
  ^loop(%i: i32):
    %done: i1 = int.cmp.eq %i, %zero
    %next: i32 = int.sub.nsw %i, %one
    cf.cond_br %done, ^out(%i), ^loop(%next)
  ^out(%o: i32):
    cf.yield %o
  }
  func.ret %r
}
