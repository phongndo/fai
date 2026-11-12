// `cf.switch` jumps to the case whose key is the value, or to the default. Keys are taken modulo
// 2^N, so -1 and 255 are the same `i8` key. C's fall-through is a jump to the next case's block.
// run: @fall(0) -> returned i32 100
// run: @fall(1) -> returned i32 3
// run: @fall(2) -> returned i32 2
// run: @fall(3) -> returned i32 100
// run: @fall(poison) -> ub poison @5:5 (branch on poison)
// run: @bytes(-1) -> returned i8 1
// run: @bytes(255) -> returned i8 1
// run: @bytes(7) -> returned i8 0
// run: @wide(-1) -> returned i128 1
// run: @wide(18446744073709551616) -> returned i128 2
// run: @wide(3) -> returned i128 3
// run: @bit(0) -> returned i32 10
// run: @bit(1) -> returned i32 11
// run: @args(1) -> returned i32 7
// run: @args(2) -> returned i32 5
// run: @args(9) -> returned i32 9

// switch (x) { case 1: r += 1; case 2: r += 2; break; default: r = 100; }
func @fall(%x: i32) -> i32 {
  %zero: i32 = int.const 0
  %r: i32 = cf.blocks {
  ^entry:
    cf.switch %x, default ^other, [1: ^one(%zero), 2: ^two(%zero)] @5:5
  ^one(%a: i32):
    %c1: i32 = int.const 1
    %a1: i32 = int.add.nsw %a, %c1
    cf.br ^two(%a1)
  ^two(%b: i32):
    %c2: i32 = int.const 2
    %b2: i32 = int.add.nsw %b, %c2
    cf.yield %b2
  ^other:
    %h: i32 = int.const 100
    cf.yield %h
  }
  func.ret %r
}

func @bytes(%x: i8) -> i8 {
  %r: i8 = cf.blocks {
  ^entry:
    cf.switch %x, default ^no, [255: ^yes]
  ^yes:
    %one: i8 = int.const 1
    cf.yield %one
  ^no:
    %z: i8 = int.const 0
    cf.yield %z
  }
  func.ret %r
}

func @wide(%x: i128) -> i128 {
  %r: i128 = cf.blocks {
  ^entry:
    cf.switch %x, default ^other, [-1: ^a, 18446744073709551616: ^b]
  ^a:
    %one: i128 = int.const 1
    cf.yield %one
  ^b:
    %two: i128 = int.const 2
    cf.yield %two
  ^other:
    %three: i128 = int.const 3
    cf.yield %three
  }
  func.ret %r
}

func @bit(%c: i1) -> i32 {
  %r: i32 = cf.blocks {
  ^entry:
    cf.switch %c, default ^t, [0: ^f]
  ^t:
    %eleven: i32 = int.const 11
    cf.yield %eleven
  ^f:
    %ten: i32 = int.const 10
    cf.yield %ten
  }
  func.ret %r
}

// Each target gets its own arguments.
func @args(%x: i32) -> i32 {
  %five: i32 = int.const 5
  %seven: i32 = int.const 7
  %r: i32 = cf.blocks {
  ^entry:
    cf.switch %x, default ^out(%x), [1: ^out(%seven), 2: ^out(%five)]
  ^out(%v: i32):
    cf.yield %v
  }
  func.ret %r
}
