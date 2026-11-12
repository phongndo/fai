// Hand-written AArch64 LFIR with floats: FP registers `d0`…`d31` (`s` or `d` by the op's format),
// float arguments in `d0`…`d7`, results in `d0`, `d1` when all are floats of one format and in
// `x0`, `x1` otherwise, and Arm's NaN rules: the first signaling NaN operand, else the first quiet
// one, made quiet; the default (canonical) NaN for invalid operations.
// run: @hyp(3.0, 4.0) -> returned f64 5.0
// run: @add(nan(0x1), 1.0) -> returned f32 nan(0x400001)
// run: @add(-nan(0x400002), nan(0x3)) -> returned f32 nan(0x400003)
// run: @add(-nan(0x400002), nan(0x400003)) -> returned f32 -nan(0x400002)
// run: @add(inf, -inf) -> returned f32 nan
// run: @mixed(-3, 0.5, 10, 2.75) -> returned f64 -2.5, i64 12
// run: @mixed(0, 0.0, 1, nan) -> returned f64 0.0, i64 1
// run: @uno(nan, 1.0) -> returned i1 1
// run: @uno(1.0, 2.0) -> returned i1 0
// run: @consts() -> returned f64 1.0, f64 -1.5
// run: @narrow(nan(0x20000000)) -> returned f32 nan(0x400001)
// run: @narrow(1e300) -> returned f32 inf
// run: @narrow(0.1) -> returned f32 0.1
// run: @mem() -> returned f64 5.0
// run: @fma(0.0, inf, nan) -> returned f64 nan
// run: @fma(1.0, inf, nan(0x5)) -> returned f64 nan(0x8000000000005)
// run: @sel(1.5, 2.5) -> returned f64 1.5, f64 2.5
// run: @callsqrt(2.0) -> @sqrt(f64 2.0) -> f64 0.0; returned f64 0.0
// run: @many(1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.5, 10.5) -> returned f64 21.0
// run: @class() -> stuck: x0 is not an FP register
// run: @clobber() -> stuck: @clobber doesn't preserve d8
layer lfir aarch64

global @g: f64 = 2.5
extern func @sqrt(f64) -> f64 effects[] assume

func @hyp(%a: f64, %b: f64) -> f64 {
  aarch64.code {
  ^entry:
    aarch64.fmul.d d2, d1, d1
    aarch64.fmadd.d d2, d0, d0
    aarch64.fsqrt.d d0, d2
    aarch64.ret
  }
}

func @add(%a: f32, %b: f32) -> f32 {
  aarch64.code {
  ^entry:
    aarch64.fadd.s d0, d0, d1
    aarch64.ret
  }
}

func @mixed(%i: i32, %x: f64, %j: i64, %y: f32) -> (f64, i64) {
  aarch64.code {
  ^entry:
    aarch64.scvtf.d.w d2, x0
    aarch64.fadd.d d0, d0, d2
    aarch64.fcvtzs.x.s x2, d1
    aarch64.add.x x1, x1, x2
    aarch64.fmov.d x0, d0
    aarch64.ret
  }
}

func @class() -> f64 {
  aarch64.code {
  ^entry:
    aarch64.fadd.d d0, x0, d0
    aarch64.ret
  }
}

func @clobber() -> f64 {
  aarch64.code {
  ^entry:
    aarch64.fmov.imm.d d8, 112
    aarch64.ret
  }
}

func @uno(%a: f64, %b: f64) -> i1 {
  aarch64.code {
  ^entry:
    aarch64.fcmp.d d0, d1
    aarch64.csinc.vc.x x0, xzr, xzr
    aarch64.ret
  }
}

func @consts() -> (f64, f64) {
  aarch64.code {
  ^entry:
    aarch64.fmov.imm.d d0, 112
    aarch64.fmov.imm.d d1, 248
    aarch64.ret
  }
}

func @narrow(%x: f64) -> f32 {
  aarch64.code {
  ^entry:
    aarch64.fcvt.s.d d0, d0
    aarch64.ret
  }
}

func @mem() -> f64 {
  aarch64.code {
  ^entry:
    aarch64.adrl x1, @g
    aarch64.ldr.x d0, x1, 0
    aarch64.fadd.d d0, d0, d0
    aarch64.str.x d0, x1, 0
    aarch64.ldr.x d1, x1, 0
    aarch64.fmov.d d0, d1
    aarch64.ret
  }
}

func @fma(%a: f64, %b: f64, %c: f64) -> f64 {
  aarch64.code {
  ^entry:
    aarch64.fmadd.d d2, d0, d1
    aarch64.fmov.d d0, d2
    aarch64.ret
  }
}

func @sel(%a: f64, %b: f64) -> (f64, f64) {
  aarch64.code {
  ^entry:
    aarch64.fcmp.d d0, d1
    aarch64.fcsel.lt.d d2, d0, d1
    aarch64.fcsel.gt.d d1, d0, d1
    aarch64.fmov.d d0, d2
    aarch64.ret
  }
}

func @callsqrt(%x: f64) -> f64 {
  aarch64.code {
  ^entry:
    aarch64.sub.imm.x sp, sp, 16
    aarch64.str.x x30, sp, 0
    aarch64.bl @sqrt
    aarch64.ldr.x x30, sp, 0
    aarch64.add.imm.x sp, sp, 16
    aarch64.ret
  }
}

// The ninth and tenth floats are on the stack.
func @many(%a: f64, %b: f64, %c: f64, %d: f64, %e: f64, %f: f64, %g: f64, %h: f64, %i: f64, %j: f64) -> f64 {
  aarch64.code {
  ^entry:
    aarch64.ldr.x fv0, sp, 0
    aarch64.ldr.x fv1, sp, 8
    aarch64.fadd.d fv2, fv0, fv1
    aarch64.fadd.d d0, fv2, d0
    aarch64.ret
  }
}
