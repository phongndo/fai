// float.fma rounds a * b + c once: the separately rounded product would lose what fma keeps.
// run: @fma(0.1, 10.0, -1.0) -> returned f64 5.551115123125783e-17
// run: @mul_add(0.1, 10.0, -1.0) -> returned f64 0.0
// (1 + 2^-27)^2 - (1 + 2^-26) is exactly 2^-54.
// run: @fma(1.0000000074505806, 1.0000000074505806, -1.0000000149011612) -> returned f64 5.551115123125783e-17
// run: @mul_add(1.0000000074505806, 1.0000000074505806, -1.0000000149011612) -> returned f64 0.0
// An exact zero is +0 unless both the product and the addend are negative zeros.
// run: @fma(2.0, 3.0, -6.0) -> returned f64 0.0
// run: @fma(-0.0, 1.0, -0.0) -> returned f64 -0.0
// run: @fma(-0.0, 1.0, 0.0) -> returned f64 0.0
// The product isn't rounded on its own, so it doesn't overflow when c brings it back.
// run: @fma(1e308, 3.0, -1.7976931348623157e308) -> returned f64 1.2023068651376843e308
// run: @mul_add(1e308, 3.0, -1.7976931348623157e308) -> returned f64 inf
// 0 * inf is invalid even when c is infinite; inf - inf is too.
// run: @fma(0.0, inf, 1.0) -> returned f64 nan
// run: @fma(inf, 0.0, inf) -> returned f64 nan
// run: @fma(inf, 2.0, -inf) -> returned f64 nan
// run: @fma(inf, -2.0, -inf) -> returned f64 -inf
// run: @fma(1.0, 2.0, inf) -> returned f64 inf
// run: @fma(nan(0x5), 0.0, inf) -> returned f64 nan
// run: @fma(5e-324, 0.5, 0.0) -> returned f64 0.0
// run: @fma(5e-324, 0.5, -0.0) -> returned f64 0.0
// run: @fma32(16777216.0, 1.0, 1.0) -> returned f32 16777216.0
// float.sqrt rounds the exact root once; the root of a negative number (not -0) is NaN.
// run: @sqrt(2.0) -> returned f64 1.4142135623730951
// run: @sqrt(4.0) -> returned f64 2.0
// run: @sqrt(-0.0) -> returned f64 -0.0
// run: @sqrt(-1.0) -> returned f64 nan
// run: @sqrt(-5e-324) -> returned f64 nan
// run: @sqrt(5e-324) -> returned f64 2.2227587494850775e-162
// run: @sqrt(1e-323) -> returned f64 3.1434555694052576e-162
// run: @sqrt(2.225073858507201e-308) -> returned f64 1.4916681462400412e-154
// run: @sqrt(inf) -> returned f64 inf
// run: @sqrt(-inf) -> returned f64 nan
// run: @sqrt(1.7976931348623157e308) -> returned f64 1.3407807929942596e154
// run: @sqrt32(2.0) -> returned f32 1.4142135
// run: @sqrt32(1e-45) -> returned f32 3.743392e-23
// run: @sqrt32(3.4028235e38) -> returned f32 1.8446743e19
func @fma(%a: f64, %b: f64, %c: f64) -> f64 {
  %r: f64 = float.fma %a, %b, %c
  func.ret %r
}

func @mul_add(%a: f64, %b: f64, %c: f64) -> f64 {
  %m: f64 = float.mul %a, %b
  %r: f64 = float.add %m, %c
  func.ret %r
}

func @fma32(%a: f32, %b: f32, %c: f32) -> f32 {
  %r: f32 = float.fma %a, %b, %c
  func.ret %r
}

func @sqrt(%a: f64) -> f64 {
  %r: f64 = float.sqrt %a
  func.ret %r
}

func @sqrt32(%a: f32) -> f32 {
  %r: f32 = float.sqrt %a
  func.ret %r
}
