// Exceptions (decision: Exceptions): `cf.try { … } catch(%e: ptr) { … }` catches what
// `exn.throw` throws in its first region or in a function called from it. An exception is a
// pointer. Unwinding ends the stack memory of the frames it leaves; an exception that leaves
// the function the run started in ends the run with `threw`.

global @err: i32 = 7
global @slot: ptr = null

func @thrower(%k: i32) -> i32 {
  %z: i32 = int.const 0 @1:1
  %is0: i1 = int.cmp.eq %k, %z @2:1
  cf.if %is0 {
    %e: ptr = mem.global @err @3:1
    exn.throw %e @4:1
  } else {
    cf.yield
  }
  func.ret %k @5:1
}

func @direct(%k: i32) -> i32 {
  %r: i32 = cf.try {
    %v: i32 = func.call @thrower(%k) @6:1
    cf.yield %v @7:1
  } catch(%e: ptr) {
    %x: i32 = mem.load %e, align 4 @8:1
    %y: i32 = int.add.wrap %x, %x @9:1
    cf.yield %y @10:1
  }
  func.ret %r @12:1
}

func @uncaught(%k: i32) -> i32 {
  %v: i32 = func.call @thrower(%k) @13:1
  func.ret %v @14:1
}

// A throw out of a loop, caught around it: the loop's results never arrive.
func @from_loop(%n: i32) -> i32 {
  %z: i32 = int.const 0 @15:1
  %one: i32 = int.const 1 @16:1
  %r: i32 = cf.try {
    %i: i32 = cf.loop iter(%j: i32 = %z) {
      %done: i1 = int.cmp.eq %j, %n @17:1
      cf.if %done {
        %four: i64 = int.const 4 @18:1
        %p: ptr = mem.alloc.trap c.malloc %four, align 4 @18:2
        mem.store i32 %j, %p, align 4 @19:1
        exn.throw %p @20:1
      } else {
        cf.yield
      }
      %j1: i32 = int.add.wrap %j, %one @21:1
      cf.continue %j1 @22:1
    }
    cf.yield %i @24:1
  } catch(%e: ptr) {
    %x: i32 = mem.load %e, align 4 @25:1
    mem.free c.malloc %e @26:1
    cf.yield %x @27:1
  }
  func.ret %r @29:1
}

// A throw out of cf.blocks, and out of a call inside them.
func @from_blocks(%k: i32) -> i32 {
  %r: i32 = cf.try {
    %b: i32 = cf.blocks {
    ^entry:
      %z: i32 = int.const 0 @30:1
      %c: i1 = int.cmp.slt %k, %z @31:1
      cf.cond_br %c, ^neg, ^pos @32:1
    ^neg:
      %e: ptr = ptr.null @33:1
      exn.throw %e @34:1
    ^pos:
      %v: i32 = func.call @thrower(%k) @35:1
      cf.yield %v @36:1
    }
    cf.yield %b @38:1
  } catch(%e2: ptr) {
    %n: ptr = ptr.null @39:1
    %isnull: i1 = ptr.cmp.eq %e2, %n @40:1
    %m: i32 = int.const -1 @41:1
    %x: i32 = cf.if %isnull {
      cf.yield %m @42:1
    } else {
      %l: i32 = mem.load %e2, align 4 @43:1
      cf.yield %l @44:1
    }
    cf.yield %x @46:1
  }
  func.ret %r @48:1
}

// A handler that throws again, caught by an outer cf.try; and one that throws out of the
// function.
func @rethrow(%k: i32, %outer: i1) -> i32 {
  %r: i32 = cf.if %outer {
    %a: i32 = cf.try {
      %b: i32 = cf.try {
        %v: i32 = func.call @thrower(%k) @49:1
        cf.yield %v @50:1
      } catch(%e: ptr) {
        exn.throw %e @51:1
      }
      cf.yield %b @53:1
    } catch(%e3: ptr) {
      %h: i32 = int.const 100 @54:1
      cf.yield %h @55:1
    }
    cf.yield %a @57:1
  } else {
    %c: i32 = cf.try {
      %v2: i32 = func.call @thrower(%k) @58:1
      cf.yield %v2 @59:1
    } catch(%e4: ptr) {
      exn.throw %e4 @60:1
    }
    cf.yield %c @62:1
  }
  func.ret %r @64:1
}

// Unwinding ends the stack memory of the frames it leaves: the callee's slot is gone.
func @leaves_slot() {
  %s: ptr = mem.stack 4, align 4 @65:1
  %g: ptr = mem.global @slot @66:1
  mem.store ptr %s, %g, align 8 @67:1
  %n: ptr = ptr.null @68:1
  exn.throw %n @69:1
}

func @dangling() -> i32 {
  cf.try {
    func.call @leaves_slot() @70:1
  } catch(%e: ptr) {
    cf.yield @71:1
  }
  %g: ptr = mem.global @slot @73:1
  %s: ptr = mem.load %g, align 8 @74:1
  %v: i32 = mem.load %s, align 4 @75:1
  func.ret %v @76:1
}

// An extern call in a cf.try: external functions don't unwind.
extern func @ext(i32) -> i32 effects[] assume

func @with_extern(%k: i32) -> i32 {
  %r: i32 = cf.try {
    %v: i32 = func.call @ext(%k) @77:1
    %w: i32 = func.call @thrower(%v) @78:1
    cf.yield %w @79:1
  } catch(%e: ptr) {
    %t: i32 = int.const 5 @80:1
    cf.yield %t @81:1
  }
  func.ret %r @83:1
}

// run: @direct(3) -> returned i32 3
// run: @direct(0) -> returned i32 14
// run: @uncaught(2) -> returned i32 2
// run: @uncaught(0) -> threw ptr #1
// run: @from_loop(4) -> returned i32 4
// run: @from_blocks(-1) -> returned i32 -1
// run: @from_blocks(0) -> returned i32 7
// run: @from_blocks(9) -> returned i32 9
// run: @rethrow(0, 1) -> returned i32 100
// run: @rethrow(0, 0) -> threw ptr #1
// run: @rethrow(6, 0) -> returned i32 6
// run: @dangling() -> ub use-after-free @75:1 (stack memory from @65:1, whose region has ended)
// run: @with_extern(1) -> @ext(i32 1) -> i32 0; returned i32 5
