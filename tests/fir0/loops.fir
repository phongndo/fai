// A loop that never exits. With `progress` that's UB; without it, the program just runs forever.
// The reference tool can't run forever, so it stops after its step budget.
// run: @spin_progress() -> out of fuel after 1000000 steps in a progress loop
// run: @spin() -> out of fuel after 1000000 steps
// run: @countdown(5) -> returned i32 0
func @spin_progress() {
  cf.loop progress {
    cf.continue
  }
  func.ret
}

func @spin() {
  cf.loop {
    cf.continue
  }
  func.ret
}

func @countdown(%n: i32) -> i32 {
  %one: i32 = int.const 1
  %zero: i32 = int.const 0
  %r: i32 = cf.loop iter(%i: i32 = %n) {
    %done: i1 = int.cmp.eq %i, %zero
    cf.if %done {
      cf.break %i
    }
    %next: i32 = int.sub.nsw %i, %one
    cf.continue %next
  }
  func.ret %r
}
