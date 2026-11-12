// NaN results of arithmetic are the oracle's choice between the canonical NaN and a quieted input
// NaN; the oracle that answers 0 picks the canonical one, `nan` (decision: NaN determinism). The
// ops that only copy bits keep every payload, signaling NaNs and sign bits included.
// run: @arith(nan(0x1), 1.0) -> returned f32 nan, f32 nan, f32 nan, f32 nan, f32 nan
// run: @arith(-nan(0x7ffff), -nan) -> returned f32 nan, f32 nan, f32 nan, f32 nan, f32 nan
// run: @arith(1.0, nan(0x400001)) -> returned f32 nan, f32 nan, f32 nan, f32 nan, f32 nan
// run: @unary(nan(0x1)) -> returned f32 -nan(0x1), f32 nan(0x1), f32 nan, f32 nan(0x1)
// run: @unary(-nan(0x123)) -> returned f32 nan(0x123), f32 nan(0x123), f32 nan, f32 -nan(0x123)
// run: @unary(-2.0) -> returned f32 2.0, f32 2.0, f32 nan, f32 -2.0
// run: @unary(-0.0) -> returned f32 0.0, f32 0.0, f32 -0.0, f32 -0.0
// run: @copysign(nan(0x1), -1.0) -> returned f32 -nan(0x1)
// run: @copysign(-nan(0x5), 0.0) -> returned f32 nan(0x5)
// run: @copysign(3.0, -nan) -> returned f32 -3.0
// run: @copysign(-0.0, inf) -> returned f32 0.0
// run: @bits(2143289345) -> returned f32 nan(0x400001), i32 2143289345
// run: @bits(-4194304) -> returned f32 -nan, i32 -4194304
// run: @bits(2139095041) -> returned f32 nan(0x1), i32 2139095041
// run: @memory(nan(0x1)) -> returned f64 nan(0x1), i64 9218868437227405313, b64 (0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0xf0, 0x7f)
// run: @memory(-nan(0x400001)) -> returned f64 -nan(0x400001), i64 -4503599623176191, b64 (0x1, 0x0, 0x40, 0x0, 0x0, 0x0, 0xf0, 0xff)
// run: @select(1, nan(0x2), 1.0) -> returned f64 nan(0x2)
// run: @select(0, 1.0, -nan(0x3)) -> returned f64 -nan(0x3)
// run: @select(poison, 1.0, 2.0) -> returned f64 poison
// run: @cvt(nan(0x1)) -> returned f64 nan, f32 nan
// run: @cvt(-nan(0x7fffff)) -> returned f64 nan, f32 nan
// Every predicate with a NaN operand: the ordered ones and `ord` are 0, the unordered ones and
// `uno` 1.
// run: @cmps(nan, 1.0) -> returned i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1
// run: @cmps(1.0, -nan(0x1)) -> returned i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1
// run: @cmps(nan, nan) -> returned i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 0, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1, i1 1
// And without one: -0 equals +0.
// run: @cmps(-0.0, 0.0) -> returned i1 1, i1 0, i1 0, i1 1, i1 0, i1 1, i1 1, i1 1, i1 0, i1 0, i1 1, i1 0, i1 1, i1 0
// run: @cmps(1.0, 2.0) -> returned i1 0, i1 1, i1 1, i1 1, i1 0, i1 0, i1 1, i1 0, i1 1, i1 1, i1 1, i1 0, i1 0, i1 0
// run: @cmps(inf, 2.0) -> returned i1 0, i1 1, i1 0, i1 0, i1 1, i1 1, i1 1, i1 0, i1 1, i1 0, i1 0, i1 1, i1 1, i1 0
// run: @cmps(-inf, -inf) -> returned i1 1, i1 0, i1 0, i1 1, i1 0, i1 1, i1 1, i1 1, i1 0, i1 0, i1 1, i1 0, i1 1, i1 0
// run: @cmps(poison, 1.0) -> returned i1 poison, i1 poison, i1 poison, i1 poison, i1 poison, i1 poison, i1 poison, i1 poison, i1 poison, i1 poison, i1 poison, i1 poison, i1 poison, i1 poison
func @arith(%a: f32, %b: f32) -> (f32, f32, f32, f32, f32) {
  %s: f32 = float.add %a, %b
  %d: f32 = float.sub %a, %b
  %m: f32 = float.mul %a, %b
  %q: f32 = float.div %a, %b
  %f: f32 = float.fma %a, %b, %b
  func.ret %s, %d, %m, %q, %f
}

func @unary(%a: f32) -> (f32, f32, f32, f32) {
  %n: f32 = float.neg %a
  %b: f32 = float.abs %a
  %s: f32 = float.sqrt %a
  %c: f32 = copy %a
  func.ret %n, %b, %s, %c
}

func @copysign(%a: f32, %b: f32) -> f32 {
  %r: f32 = float.copysign %a, %b
  func.ret %r
}

func @bits(%x: i32) -> (f32, i32) {
  %f: f32 = float.from_bits %x
  %b: i32 = float.to_bits %f
  func.ret %f, %b
}

func @memory(%x: f64) -> (f64, i64, b64) {
  %p: ptr = mem.stack 8, align 8
  mem.store f64 %x, %p, align 8
  %y: f64 = mem.load %p, align 8
  %i: i64 = mem.load %p, align 8
  %b: b64 = mem.load %p, align 8
  func.ret %y, %i, %b
}

func @select(%c: i1, %a: f64, %b: f64) -> f64 {
  %r: f64 = select %c, %a, %b
  func.ret %r
}

func @cvt(%a: f32) -> (f64, f32) {
  %e: f64 = float.ext %a
  %t: f32 = float.trunc %e
  func.ret %e, %t
}

func @cmps(%a: f64, %b: f64) -> (i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1, i1) {
  %oeq: i1 = float.cmp.oeq %a, %b
  %one: i1 = float.cmp.one %a, %b
  %olt: i1 = float.cmp.olt %a, %b
  %ole: i1 = float.cmp.ole %a, %b
  %ogt: i1 = float.cmp.ogt %a, %b
  %oge: i1 = float.cmp.oge %a, %b
  %ord: i1 = float.cmp.ord %a, %b
  %ueq: i1 = float.cmp.ueq %a, %b
  %une: i1 = float.cmp.une %a, %b
  %ult: i1 = float.cmp.ult %a, %b
  %ule: i1 = float.cmp.ule %a, %b
  %ugt: i1 = float.cmp.ugt %a, %b
  %uge: i1 = float.cmp.uge %a, %b
  %uno: i1 = float.cmp.uno %a, %b
  func.ret %oeq, %one, %olt, %ole, %ogt, %oge, %ord, %ueq, %une, %ult, %ule, %ugt, %uge, %uno
}
