// Jumps between labeled blocks. `cf.blocks` runs its first block; `cf.br`, `cf.cond_br`, and
// `cf.switch` jump to a block of the nearest `cf.blocks` with arguments for its parameters, and
// `cf.yield` leaves with the op's results. A value defined in a block is visible only there.
// run: @sum(0) -> returned i32 0
// run: @sum(5) -> returned i32 10
// run: @sum(poison) -> ub poison @6:5 (branch on poison)
// run: @classify(-4) -> returned i8 -1
// run: @classify(0) -> returned i8 0
// run: @classify(9) -> returned i8 1
// run: @early(3) -> returned i32 3
// run: @early(-3) -> returned i32 0
// run: @leave_loop(7) -> returned i32 4
// run: @in_loop(3) -> returned i32 6
// run: @goto_out(5) -> returned i32 5
// run: @goto_out(50) -> returned i32 -1
func @sum(%n: i32) -> i32 {
  %zero: i32 = int.const 0
  %one: i32 = int.const 1
  %r: i32 = cf.blocks {
  ^entry:
    cf.br ^head(%zero, %zero)
  ^head(%i: i32, %acc: i32):
    %done: i1 = int.cmp.sge %i, %n
    cf.cond_br %done, ^exit(%acc), ^body(%i, %acc) @6:5
  ^body(%k: i32, %s: i32):
    // A back edge: ^head starts again with new arguments.
    %s2: i32 = int.add.nsw %s, %k
    %k2: i32 = int.add.nsw %k, %one
    cf.br ^head(%k2, %s2)
  ^exit(%a: i32):
    cf.yield %a
  }
  func.ret %r
}

// Three ways out of a block: one result per path.
func @classify(%x: i32) -> i8 {
  %zero: i32 = int.const 0
  %r: i8 = cf.blocks {
  ^entry:
    %neg: i1 = int.cmp.slt %x, %zero
    cf.cond_br %neg, ^minus, ^nonneg
  ^nonneg:
    %z: i1 = int.cmp.eq %x, %zero
    cf.cond_br %z, ^zero, ^plus
  ^minus:
    %m: i8 = int.const -1
    cf.yield %m
  ^zero:
    %o: i8 = int.const 0
    cf.yield %o
  ^plus:
    %p: i8 = int.const 1
    cf.yield %p
  }
  func.ret %r
}

// `func.ret` leaves the function from inside a block.
func @early(%x: i32) -> i32 {
  %zero: i32 = int.const 0
  cf.blocks {
  ^entry:
    %neg: i1 = int.cmp.slt %x, %zero
    cf.cond_br %neg, ^clamp, ^done
  ^clamp:
    func.ret %zero
  ^done:
    cf.yield
  }
  func.ret %x
}

// `cf.break` leaves a loop from inside a block, after jumping around in it.
func @leave_loop(%x: i32) -> i32 {
  %four: i32 = int.const 4
  %r: i32 = cf.loop {
    cf.blocks {
    ^a:
      cf.br ^b
    ^b:
      cf.break %four
    }
    cf.continue
  }
  func.ret %r
}

// A cf.blocks inside a loop body: each iteration runs it again.
func @in_loop(%n: i32) -> i32 {
  %zero: i32 = int.const 0
  %one: i32 = int.const 1
  %r: i32 = cf.loop iter(%i: i32 = %zero, %acc: i32 = %zero) {
    %done: i1 = int.cmp.sge %i, %n
    cf.if %done {
      cf.break %acc
    }
    %i2: i32 = int.add.nsw %i, %one
    %acc2: i32 = cf.blocks {
    ^entry:
      cf.br ^add(%i2)
    ^add(%v: i32):
      %s: i32 = int.add.nsw %acc, %v
      cf.yield %s
    }
    cf.continue %i2, %acc2
  }
  func.ret %r
}

// A jump out of a structured loop and a cf.if inside a block, to another block: like C's
// `goto` out of nested statements.
func @goto_out(%n: i32) -> i32 {
  %zero: i32 = int.const 0
  %one: i32 = int.const 1
  %ten: i32 = int.const 10
  %r: i32 = cf.blocks {
  ^entry:
    %found: i32 = cf.loop iter(%i: i32 = %zero) {
      %big: i1 = int.cmp.sge %i, %ten
      cf.if %big {
        cf.br ^fail
      }
      %hit: i1 = int.cmp.eq %i, %n
      cf.if %hit {
        cf.break %i
      }
      %i2: i32 = int.add.nsw %i, %one
      cf.continue %i2
    }
    cf.br ^ok(%found)
  ^ok(%v: i32):
    cf.yield %v
  ^fail:
    %m: i32 = int.const -1
    cf.yield %m
  }
  func.ret %r
}
