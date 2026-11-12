// MFIR's form of exceptions: a call that may throw names its handler, a block of the nearest
// `cf.blocks` that takes the exception (`func.invoke`, `func.invoke.indirect`); a plain call
// passes exceptions on to its caller, and `exn.throw` unwinds out of the function.
layer mfir

global @err: i32 = 7

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

func @pass(%k: i32) -> i32 {
  %v: i32 = func.call @thrower(%k) @6:1
  %one: i32 = int.const 1 @7:1
  %w: i32 = int.add.wrap %v, %one @8:1
  func.ret %w @9:1
}

func @handle(%k: i32, %indirect: i1) -> i32 {
  %f: ptr = func.addr @pass @10:1
  %r: i32 = cf.blocks {
  ^entry:
    cf.cond_br %indirect, ^ind, ^dir @11:1
  ^dir:
    %v: i32 = func.invoke @pass(%k) unwind ^catch @12:1
    cf.yield %v @13:1
  ^ind:
    %u: i32 = func.invoke.indirect func<(i32) -> i32> %f(%k) unwind ^catch @14:1
    cf.yield %u @15:1
  ^catch(%e: ptr):
    %x: i32 = mem.load %e, align 4 @16:1
    %m: i32 = int.const -1 @17:1
    %y: i32 = int.mul.wrap %x, %m @18:1
    cf.yield %y @19:1
  }
  func.ret %r @20:1
}

// run: @pass(4) -> returned i32 5
// run: @pass(0) -> threw ptr #1
// run: @handle(4, 0) -> returned i32 5
// run: @handle(0, 0) -> returned i32 -7
// run: @handle(4, 1) -> returned i32 5
// run: @handle(0, 1) -> returned i32 -7
