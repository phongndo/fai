// A block's stack memory ends when control leaves the block, by a jump (back edges included) or
// by leaving the `cf.blocks`. A jump back to a block gets fresh memory.
// run: @kept() -> returned i32 5
// run: @dangling() -> ub use-after-free @6:5 (stack memory from @3:5, whose region has ended)
// run: @fresh() -> returned i32 poison
func @kept() -> i32 {
  %p: ptr = mem.stack 4, align 4
  %five: i32 = int.const 5
  cf.blocks {
  ^entry:
    mem.store i32 %five, %p, align 4
    cf.br ^next
  ^next:
    cf.yield
  }
  %v: i32 = mem.load %p, align 4
  func.ret %v
}

func @dangling() -> i32 {
  %r: i32 = cf.blocks {
  ^entry:
    %p: ptr = mem.stack 4, align 4 @3:5
    cf.br ^use(%p)
  ^use(%q: ptr):
    %v: i32 = mem.load %q, align 4 @6:5
    cf.yield %v
  }
  func.ret %r
}

// The second time through ^a, its memory is new, so the load sees nothing stored.
func @fresh() -> i32 {
  %zero: i1 = int.const 0
  %one: i1 = int.const 1
  %r: i32 = cf.blocks {
  ^entry:
    cf.br ^a(%zero)
  ^a(%again: i1):
    %p: ptr = mem.stack 4, align 4
    cf.if %again {
    } else {
      %seven: i32 = int.const 7
      mem.store i32 %seven, %p, align 4
    }
    %v: i32 = mem.load %p, align 4
    cf.cond_br %again, ^done(%v), ^a(%one)
  ^done(%x: i32):
    cf.yield %x
  }
  func.ret %r
}
