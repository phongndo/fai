// The AArch64 backend's edge cases: every run here is also compiled and run natively, and its
// LFIR before and after register allocation is run in the interpreter (see
// tests/rust/aarch64.rs).
// run: @add8_trap(100, 100) -> trap overflow @1:1
// run: @add8_trap(100, -100) -> returned i8 0
// run: @add8_usat(200, 100) -> returned i8 -1
// run: @sub7_ssat(-60, 10) -> returned i7 -64
// run: @sub7_ssat(60, -10) -> returned i7 63
// run: @add32_utrap(-1, 1) -> trap overflow @2:1
// run: @sub64_strap(-9223372036854775808, 1) -> trap overflow @3:1
// run: @mul48_ssat(100000000, -100000000) -> returned i48 -140737488355328
// run: @mul48_ssat(1000, 1000) -> returned i48 1000000
// run: @mul64_utrap(4294967296, 4294967296) -> trap overflow @4:1
// run: @mul64_utrap(4294967295, 4294967297) -> returned i64 -1
// run: @mul64_ssat(-4294967296, 4294967296) -> returned i64 -9223372036854775808
// run: @div8(-128, -1) -> trap overflow @5:1
// run: @div8(7, 0) -> trap div0 @5:1
// run: @div8(-7, 2) -> returned i8 -3
// run: @rem8_total(-128, -1) -> returned i8 0
// run: @rem8_total(5, 0) -> returned i8 5
// run: @div64_wrap(-9223372036854775808, -1) -> returned i64 -9223372036854775808
// run: @div64_wrap(1, 0) -> trap div0 @6:1
// run: @remu32(-1, 10) -> returned i32 5
// run: @shl7_mask(1, 9) -> returned i7 4
// run: @shrs8_total(-128, 200) -> returned i8 -1
// run: @shrs8_total(-128, 3) -> returned i8 -16
// run: @shru64_total(-1, 64) -> returned i64 0
// run: @shru64_total(-1, 63) -> returned i64 1
// run: @shl32_trap(1, 32) -> trap shift @7:1
// run: @shl1_mask(1, 1) -> returned i1 1
// run: @narrow_cmp(100, 100) -> returned i1 1, i1 0, i16 200, i16 -56
// run: @narrow_cmp(-1, -1) -> returned i1 1, i1 1, i16 254, i16 -2
// run: @call_many(5) -> returned i64 7
// run: @overlap(3) -> returned i8 50, i8 107, i8 -107
// run: @overlap(-3) -> returned i8 50, i8 107, i8 -107
// run: @classify(-7) -> returned i32 1
// run: @classify(9) -> returned i32 4
// run: @classify(30000) -> returned i32 7
// run: @classify(-32768) -> returned i32 8
// run: @classify(4) -> returned i32 0
// run: @heap(100) -> returned i8 42
// run: @pressure(3) -> returned i64 9408
layer mfir

func @add8_trap(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.add.s.trap %a, %b @1:1
  func.ret %r
}

func @add8_usat(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.add.u.sat %a, %b
  func.ret %r
}

func @sub7_ssat(%a: i7, %b: i7) -> i7 {
  %r: i7 = int.sub.s.sat %a, %b
  func.ret %r
}

func @add32_utrap(%a: i32, %b: i32) -> i32 {
  %r: i32 = int.add.u.trap %a, %b @2:1
  func.ret %r
}

func @sub64_strap(%a: i64, %b: i64) -> i64 {
  %r: i64 = int.sub.s.trap %a, %b @3:1
  func.ret %r
}

func @mul48_ssat(%a: i48, %b: i48) -> i48 {
  %r: i48 = int.mul.s.sat %a, %b
  func.ret %r
}

func @mul64_utrap(%a: i64, %b: i64) -> i64 {
  %r: i64 = int.mul.u.trap %a, %b @4:1
  func.ret %r
}

func @mul64_ssat(%a: i64, %b: i64) -> i64 {
  %r: i64 = int.mul.s.sat %a, %b
  func.ret %r
}

func @div8(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.div.s.trap %a, %b @5:1
  func.ret %r
}

func @rem8_total(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.rem.s.total %a, %b
  func.ret %r
}

func @div64_wrap(%a: i64, %b: i64) -> i64 {
  %r: i64 = int.div.s.trap.wrap %a, %b @6:1
  func.ret %r
}

func @remu32(%a: i32, %b: i32) -> i32 {
  %r: i32 = int.rem.u.total %a, %b
  func.ret %r
}

func @shl7_mask(%a: i7, %b: i7) -> i7 {
  %r: i7 = int.shl.mask %a, %b
  func.ret %r
}

func @shrs8_total(%a: i8, %b: i8) -> i8 {
  %r: i8 = int.shr.s.total %a, %b
  func.ret %r
}

func @shru64_total(%a: i64, %b: i64) -> i64 {
  %r: i64 = int.shr.u.total %a, %b
  func.ret %r
}

func @shl32_trap(%a: i32, %b: i32) -> i32 {
  %r: i32 = int.shl.trap %a, %b @7:1
  func.ret %r
}

func @shl1_mask(%a: i1, %b: i1) -> i1 {
  %r: i1 = int.shl.mask %a, %b
  func.ret %r
}

// Narrow values whose upper register bits are left over from wrapping arithmetic.
func @narrow_cmp(%a: i8, %b: i8) -> (i1, i1, i16, i16) {
  %s: i8 = int.add.wrap %a, %b
  %lt: i1 = int.cmp.slt %s, %a
  %ult: i1 = int.cmp.ult %s, %a
  %z: i16 = int.zext %s
  %x: i16 = int.sext %s
  func.ret %lt, %ult, %z, %x
}

func @many(%a0: i64, %a1: i32, %a2: i8, %a3: i64, %a4: i64, %a5: i64, %a6: i64, %a7: i64, %a8: i16, %a9: i64) -> (i64, i16, i64) {
  %s: i64 = int.add.wrap %a0, %a9
  %t: i16 = int.sub.wrap %a8, %a8
  %u: i16 = int.add.wrap %t, %a8
  func.ret %s, %u, %a7
}

func @call_many(%x: i64) -> i64 {
  %c1: i32 = int.const 1
  %c2: i8 = int.const 2
  %c8: i16 = int.const -8
  %r0: i64, %r1: i16, %r2: i64 = func.call @many(%x, %c1, %c2, %x, %x, %x, %x, %x, %c8, %x)
  %w: i64 = int.sext %r1
  %s: i64 = int.add.wrap %r0, %w
  %t: i64 = int.add.wrap %s, %r2
  func.ret %t
}

// Overlapping copies of 100 bytes, both directions.
func @overlap(%shift: i64) -> (i8, i8, i8) {
  %buf: ptr = mem.stack 256, align 8
  %i0: i64 = int.const 0
  %n: i64 = int.const 200
  %done: i64 = cf.loop iter(%i: i64 = %i0) {
    %end: i1 = int.cmp.uge %i, %n
    cf.if %end {
      cf.break %i
    } else {
    }
    %p: ptr = ptr.offset.inbounds %buf, %i
    %b: i8 = int.trunc.wrap %i
    mem.store i8 %b, %p, align 1
    %one: i64 = int.const 1
    %j: i64 = int.add.wrap %i, %one
    cf.continue %j
  }
  %fifty: i64 = int.const 50
  %src: ptr = ptr.offset.inbounds %buf, %fifty
  %dst: ptr = ptr.offset.inbounds %src, %shift
  mem.copy array<100 x i8> %dst, %src, align 1
  %r0: i8 = mem.load %dst, align 1
  %k: i64 = int.const 57
  %q: ptr = ptr.offset.inbounds %dst, %k
  %r1: i8 = mem.load %q, align 1
  %k2: i64 = int.const 99
  %q2: ptr = ptr.offset.inbounds %dst, %k2
  %r2: i8 = mem.load %q2, align 1
  func.ret %r0, %r1, %r2
}

// A switch with enough cases for a search tree, on a narrow value.
func @classify(%v: i16) -> i32 {
  %r: i32 = cf.blocks {
  ^entry:
    cf.switch %v, default ^other, [-7: ^a, 0: ^b, 3: ^c, 9: ^d, 100: ^e, 1000: ^f, 30000: ^g, -32768: ^h]
  ^a:
    %ra: i32 = int.const 1
    cf.yield %ra
  ^b:
    %rb: i32 = int.const 2
    cf.yield %rb
  ^c:
    %rc: i32 = int.const 3
    cf.yield %rc
  ^d:
    %rd: i32 = int.const 4
    cf.yield %rd
  ^e:
    %re: i32 = int.const 5
    cf.yield %re
  ^f:
    %rf: i32 = int.const 6
    cf.yield %rf
  ^g:
    %rg: i32 = int.const 7
    cf.yield %rg
  ^h:
    %rh: i32 = int.const 8
    cf.yield %rh
  ^other:
    %ro: i32 = int.const 0
    cf.yield %ro
  }
  func.ret %r
}

func @heap(%n: i64) -> i8 {
  %p: ptr = mem.alloc.trap c.malloc %n, align 64
  %v: i8 = int.const 42
  mem.store i8 %v, %p, align 1
  %r: i8 = mem.load %p, align 1
  mem.free c.malloc %p
  func.ret %r
}

func @ident(%x: i64) -> i64 {
  func.ret %x
}

func @pressure(%x: i64) -> i64 {
  %c0: i64 = int.const 3
  %v0: i64 = int.mul.wrap %x, %c0
  %c1: i64 = int.const 10
  %v1: i64 = int.mul.wrap %x, %c1
  %c2: i64 = int.const 17
  %v2: i64 = int.mul.wrap %x, %c2
  %c3: i64 = int.const 24
  %v3: i64 = int.mul.wrap %x, %c3
  %c4: i64 = int.const 31
  %v4: i64 = int.mul.wrap %x, %c4
  %c5: i64 = int.const 38
  %v5: i64 = int.mul.wrap %x, %c5
  %c6: i64 = int.const 45
  %v6: i64 = int.mul.wrap %x, %c6
  %c7: i64 = int.const 52
  %v7: i64 = int.mul.wrap %x, %c7
  %c8: i64 = int.const 59
  %v8: i64 = int.mul.wrap %x, %c8
  %c9: i64 = int.const 66
  %v9: i64 = int.mul.wrap %x, %c9
  %c10: i64 = int.const 73
  %v10: i64 = int.mul.wrap %x, %c10
  %c11: i64 = int.const 80
  %v11: i64 = int.mul.wrap %x, %c11
  %c12: i64 = int.const 87
  %v12: i64 = int.mul.wrap %x, %c12
  %c13: i64 = int.const 94
  %v13: i64 = int.mul.wrap %x, %c13
  %c14: i64 = int.const 101
  %v14: i64 = int.mul.wrap %x, %c14
  %c15: i64 = int.const 108
  %v15: i64 = int.mul.wrap %x, %c15
  %c16: i64 = int.const 115
  %v16: i64 = int.mul.wrap %x, %c16
  %c17: i64 = int.const 122
  %v17: i64 = int.mul.wrap %x, %c17
  %c18: i64 = int.const 129
  %v18: i64 = int.mul.wrap %x, %c18
  %c19: i64 = int.const 136
  %v19: i64 = int.mul.wrap %x, %c19
  %c20: i64 = int.const 143
  %v20: i64 = int.mul.wrap %x, %c20
  %c21: i64 = int.const 150
  %v21: i64 = int.mul.wrap %x, %c21
  %c22: i64 = int.const 157
  %v22: i64 = int.mul.wrap %x, %c22
  %c23: i64 = int.const 164
  %v23: i64 = int.mul.wrap %x, %c23
  %c24: i64 = int.const 171
  %v24: i64 = int.mul.wrap %x, %c24
  %c25: i64 = int.const 178
  %v25: i64 = int.mul.wrap %x, %c25
  %c26: i64 = int.const 185
  %v26: i64 = int.mul.wrap %x, %c26
  %c27: i64 = int.const 192
  %v27: i64 = int.mul.wrap %x, %c27
  %c28: i64 = int.const 199
  %v28: i64 = int.mul.wrap %x, %c28
  %c29: i64 = int.const 206
  %v29: i64 = int.mul.wrap %x, %c29
  %k: i64 = func.call @ident(%x)
  %s0: i64 = int.add.wrap %k, %v0
  %s1: i64 = int.add.wrap %s0, %v1
  %s2: i64 = int.add.wrap %s1, %v2
  %s3: i64 = int.add.wrap %s2, %v3
  %s4: i64 = int.add.wrap %s3, %v4
  %s5: i64 = int.add.wrap %s4, %v5
  %s6: i64 = int.add.wrap %s5, %v6
  %s7: i64 = int.add.wrap %s6, %v7
  %s8: i64 = int.add.wrap %s7, %v8
  %s9: i64 = int.add.wrap %s8, %v9
  %s10: i64 = int.add.wrap %s9, %v10
  %s11: i64 = int.add.wrap %s10, %v11
  %s12: i64 = int.add.wrap %s11, %v12
  %s13: i64 = int.add.wrap %s12, %v13
  %s14: i64 = int.add.wrap %s13, %v14
  %s15: i64 = int.add.wrap %s14, %v15
  %s16: i64 = int.add.wrap %s15, %v16
  %s17: i64 = int.add.wrap %s16, %v17
  %s18: i64 = int.add.wrap %s17, %v18
  %s19: i64 = int.add.wrap %s18, %v19
  %s20: i64 = int.add.wrap %s19, %v20
  %s21: i64 = int.add.wrap %s20, %v21
  %s22: i64 = int.add.wrap %s21, %v22
  %s23: i64 = int.add.wrap %s22, %v23
  %s24: i64 = int.add.wrap %s23, %v24
  %s25: i64 = int.add.wrap %s24, %v25
  %s26: i64 = int.add.wrap %s25, %v26
  %s27: i64 = int.add.wrap %s26, %v27
  %s28: i64 = int.add.wrap %s27, %v28
  %s29: i64 = int.add.wrap %s28, %v29
  func.ret %s29
}
