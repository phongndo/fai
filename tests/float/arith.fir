// Arithmetic rounds the exact result once, to nearest, ties to even (decision: Float semantics).
// run: @add64(0.1, 0.2) -> returned f64 0.30000000000000004
// run: @add64(1e308, 1e308) -> returned f64 inf
// run: @add64(-1e308, -1e308) -> returned f64 -inf
// x + (-x) is +0, and -0 + -0 is -0.
// run: @add64(1.5, -1.5) -> returned f64 0.0
// run: @add64(-0.0, -0.0) -> returned f64 -0.0
// run: @add64(-0.0, 0.0) -> returned f64 0.0
// run: @add64(inf, -inf) -> returned f64 nan
// run: @add64(inf, 1.0) -> returned f64 inf
// run: @add64(-inf, -inf) -> returned f64 -inf
// run: @add64(poison, 1.0) -> returned f64 poison
// x - x is +0; -0 - +0 is -0, and -0 - -0 is +0.
// run: @sub64(2.0, 2.0) -> returned f64 0.0
// run: @sub64(-0.0, 0.0) -> returned f64 -0.0
// run: @sub64(-0.0, -0.0) -> returned f64 0.0
// run: @sub64(inf, inf) -> returned f64 nan
// run: @sub64(1.0, inf) -> returned f64 -inf
// run: @mul64(0.1, 3.0) -> returned f64 0.30000000000000004
// run: @mul64(-0.0, 5.0) -> returned f64 -0.0
// run: @mul64(inf, 0.0) -> returned f64 nan
// run: @mul64(-inf, -2.0) -> returned f64 inf
// run: @mul64(1e-300, 1e-300) -> returned f64 0.0
// run: @mul64(-1e-300, 1e-300) -> returned f64 -0.0
// run: @div64(1.0, 3.0) -> returned f64 0.3333333333333333
// run: @div64(1.0, 0.0) -> returned f64 inf
// run: @div64(-1.0, 0.0) -> returned f64 -inf
// run: @div64(1.0, -0.0) -> returned f64 -inf
// run: @div64(0.0, 0.0) -> returned f64 nan
// run: @div64(inf, inf) -> returned f64 nan
// run: @div64(-5.0, inf) -> returned f64 -0.0
// run: @div64(inf, -2.0) -> returned f64 -inf
// run: @add32(0.1, 0.2) -> returned f32 0.3
// run: @add32(16777216.0, 1.0) -> returned f32 16777216.0
// run: @add32(16777216.0, 3.0) -> returned f32 16777220.0
// run: @mul32(3.4028235e38, 2.0) -> returned f32 inf
// run: @div32(1.0, 3.0) -> returned f32 0.33333334
// run: @div32(1e-45, 2.0) -> returned f32 0.0
// run: @div32(3e-45, 2.0) -> returned f32 1e-45
func @add64(%a: f64, %b: f64) -> f64 {
  %r: f64 = float.add %a, %b
  func.ret %r
}

func @sub64(%a: f64, %b: f64) -> f64 {
  %r: f64 = float.sub %a, %b
  func.ret %r
}

func @mul64(%a: f64, %b: f64) -> f64 {
  %r: f64 = float.mul %a, %b
  func.ret %r
}

func @div64(%a: f64, %b: f64) -> f64 {
  %r: f64 = float.div %a, %b
  func.ret %r
}

func @add32(%a: f32, %b: f32) -> f32 {
  %r: f32 = float.add %a, %b
  func.ret %r
}

func @mul32(%a: f32, %b: f32) -> f32 {
  %r: f32 = float.mul %a, %b
  func.ret %r
}

func @div32(%a: f32, %b: f32) -> f32 {
  %r: f32 = float.div %a, %b
  func.ret %r
}
