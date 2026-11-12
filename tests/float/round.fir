// Ties to even, subnormals, and overflow and underflow at the format's limits.
// 2^53 + 1 is halfway between 2^53 and 2^53 + 2: it rounds to the even significand, 2^53.
// run: @add64(9007199254740992.0, 1.0) -> returned f64 9007199254740992.0
// 2^53 + 3 is halfway between 2^53 + 2 and 2^53 + 4: it rounds up, to 2^53 + 4.
// run: @add64(9007199254740992.0, 3.0) -> returned f64 9007199254740996.0
// 1 + 2^-53 is a tie: down to 1. 1 + 3 * 2^-53 is a tie: up to 1 + 2^-51.
// run: @add64(1.0, 1.1102230246251565e-16) -> returned f64 1.0
// run: @add64(1.0, 3.3306690738754696e-16) -> returned f64 1.0000000000000004
// The smallest subnormal and the largest, and the smallest normal.
// run: @add64(5e-324, 5e-324) -> returned f64 1e-323
// run: @sub64(2.2250738585072014e-308, 5e-324) -> returned f64 2.225073858507201e-308
// run: @add64(2.225073858507201e-308, 5e-324) -> returned f64 2.2250738585072014e-308
// Half the smallest subnormal is a tie with 0, which is even; three halves round to 2 units.
// run: @mul64(5e-324, 0.5) -> returned f64 0.0
// run: @mul64(5e-324, 1.5) -> returned f64 1e-323
// run: @mul64(-5e-324, 0.5) -> returned f64 -0.0
// run: @div64(5e-324, 2.0000000000000004) -> returned f64 0.0
// The largest finite value plus half an ulp (2^970) is a tie that rounds to the even
// significand, 2^1024: infinity. Plus the next value down, it stays.
// run: @add64(1.7976931348623157e308, 9.9792015476736e291) -> returned f64 inf
// run: @add64(1.7976931348623157e308, 9.979201547673598e291) -> returned f64 1.7976931348623157e308
// f32: 2^24 + 1 is a tie, down to 2^24; the smallest subnormal halves to 0.
// run: @add32(16777216.0, 1.0) -> returned f32 16777216.0
// run: @mul32(1e-45, 0.5) -> returned f32 0.0
// run: @mul32(1e-45, 0.75) -> returned f32 1e-45
// run: @add32(3.4028235e38, 1.0141205e31) -> returned f32 inf
// run: @add32(3.4028235e38, 1.0141204e31) -> returned f32 3.4028235e38
// Constants read as the nearest value too.
// run: @consts() -> returned f64 0.0, f64 5e-324, f32 0.1, f32 16777216.0, f64 inf, f64 -0.0, f32 3.4028235e38, f64 1.2345678901234568e29, f64 0.000123
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

func @consts() -> (f64, f64, f32, f32, f64, f64, f32, f64, f64) {
  %a: f64 = float.const 2.4703282292062327e-324
  %b: f64 = float.const 2.4703282292062328e-324
  %c: f32 = float.const 0.1
  %d: f32 = float.const 16777217
  %e: f64 = float.const 1e400
  %f: f64 = float.const -1e-400
  %g: f32 = float.const 3.4028235677973366e38
  %h: f64 = float.const 123456789012345678901234567890
  %i: f64 = float.const 0.000123
  func.ret %a, %b, %c, %d, %e, %f, %g, %h, %i
}
