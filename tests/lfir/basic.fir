// Hand-written AArch64 LFIR. A function's code is `aarch64.code`: labeled blocks of machine
// instructions on registers, with explicit branches. Arguments and results are where AAPCS64
// puts them.
// run: @add(2, 3) -> returned i32 5
// run: @add(2147483647, 1) -> returned i32 -2147483648
// run: @max(-5, 3) -> returned i64 3
// run: @max(7, 3) -> returned i64 7
// run: @sum(4) -> returned i64 10
// run: @div(7, 0) -> trap div0 @3:5
// run: @div(7, 2) -> returned i32 3
// run: @store_load(9) -> returned i64 9
// run: @call() -> returned i32 42
// run: @hello() -> @puts(ptr #1) -> i32 0; returned i32 0
// run: @heap() -> returned i8 7; leak: 16 bytes from c.malloc at @2:3
layer lfir aarch64

global const @msg: array<3 x i8> = bytes "686900"
extern func @puts(ptr) -> i32 effects[read(args)] assume

func @add(%a: i32, %b: i32) -> i32 {
  aarch64.code {
  ^entry:
    aarch64.add.w x0, x0, x1
    aarch64.ret
  }
}

func @max(%a: i64, %b: i64) -> i64 {
  aarch64.code {
  ^entry:
    aarch64.subs.x xzr, x0, x1
    aarch64.b.gt ^done, ^other
  ^other:
    aarch64.mov.x x0, x1
    aarch64.b ^done
  ^done:
    aarch64.ret
  }
}

// 1 + 2 + … + n with virtual registers.
func @sum(%n: i64) -> i64 {
  aarch64.code {
  ^entry:
    aarch64.mov.x v0, x0
    aarch64.movz.x v1, 0, 0
    aarch64.b ^loop
  ^loop:
    aarch64.subs.imm.x xzr, v0, 0
    aarch64.b.eq ^done, ^body
  ^body:
    aarch64.add.x v1, v1, v0
    aarch64.sub.imm.x v0, v0, 1
    aarch64.b ^loop
  ^done:
    aarch64.mov.x x0, v1
    aarch64.ret
  }
}

func @div(%a: i32, %b: i32) -> i32 {
  aarch64.code {
  ^entry:
    aarch64.subs.imm.w xzr, x1, 0
    aarch64.b.eq ^trap, ^ok
  ^ok:
    aarch64.sdiv.w x0, x0, x1
    aarch64.ret
  ^trap:
    aarch64.trap.div0 @3:5
  }
}

// A frame: save fp and lr, store to the stack, load back.
func @store_load(%x: i64) -> i64 {
  aarch64.code {
  ^entry:
    aarch64.sub.imm.x sp, sp, 32
    aarch64.str.x x29, sp, 16
    aarch64.str.x x30, sp, 24
    aarch64.add.imm.x x29, sp, 16
    aarch64.str.x x0, sp, 0
    aarch64.movz.x x0, 0, 0
    aarch64.ldr.x x0, sp, 0
    aarch64.ldr.x x29, sp, 16
    aarch64.ldr.x x30, sp, 24
    aarch64.add.imm.x sp, sp, 32
    aarch64.ret
  }
}

func @forty_two() -> i32 {
  aarch64.code {
  ^entry:
    aarch64.movz.w x0, 42, 0
    aarch64.ret
  }
}

func @call() -> i32 {
  aarch64.code {
  ^entry:
    aarch64.bl @forty_two
    aarch64.ret
  }
}

func @hello() -> i32 {
  aarch64.code {
  ^entry:
    aarch64.adrl x0, @msg
    aarch64.bl @puts
    aarch64.ret
  }
}

func @heap() -> i8 {
  aarch64.code {
  ^entry:
    aarch64.movz.x x0, 16, 0
    aarch64.bl.alloc c.malloc, align 16 @2:3
    aarch64.movz.w x1, 7, 0
    aarch64.str.b x1, x0, 3
    aarch64.ldr.b x0, x0, 3
    aarch64.ret
  }
}
