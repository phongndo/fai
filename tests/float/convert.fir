// float.to_int takes the integer part (toward zero); NaN and an integer part out of the result's
// range are the edge cases: UB (`.ub`), the nearest bound with NaN at 0 (`.sat`), or a trap with
// reason `convert` (`.trap`). A poison input is UB for `.ub` and `.trap`.
// run: @s8(127.9) -> returned i8 127
// run: @s8(-128.9) -> returned i8 -128
// run: @s8(128.0) -> returned i8 127
// run: @s8(-129.0) -> returned i8 -128
// run: @s8(-0.0) -> returned i8 0
// run: @s8(inf) -> returned i8 127
// run: @s8(-inf) -> returned i8 -128
// run: @s8(nan) -> returned i8 0
// run: @s8(poison) -> returned i8 poison
// run: @s8ub(128.0) -> ub convert
// run: @s8ub(nan) -> ub convert
// run: @s8ub(-128.5) -> returned i8 -128
// run: @s8ub(poison) -> ub poison
// run: @s8trap(-129.0) -> trap convert
// run: @s8trap(nan(0x1)) -> trap convert
// run: @s8trap(poison) -> ub poison
// Unsigned: -0.9 truncates to 0, which is in range; -1 is not.
// run: @u8(255.5) -> returned i8 -1
// run: @u8(256.0) -> returned i8 -1
// run: @u8(-0.9) -> returned i8 0
// run: @u8(-1.0) -> returned i8 0
// run: @u8(-inf) -> returned i8 0
// run: @u8(nan) -> returned i8 0
// run: @u8trap(-1.0) -> trap convert
// 64-bit limits: 2^63 is out of range for i64, -2^63 is in; 2^64 for u64.
// run: @s64(9223372036854775807.0) -> trap convert
// run: @s64(-9223372036854775808.0) -> returned i64 -9223372036854775808, i64 -9223372036854775808
// run: @s64(-9223372036854777856.0) -> trap convert
// run: @s64(9223372036854774784.0) -> returned i64 9223372036854774784, i64 9223372036854774784
// run: @u64(18446744073709551615.0) -> returned i64 -1
// run: @u64(18446744073709549568.0) -> returned i64 -2048
// run: @u64(1e300) -> returned i64 -1
// run: @u64ub(18446744073709551616.0) -> ub convert
// Wider than 64 bits, and odd widths.
// run: @wide(1e30) -> returned i128 1000000000000000019884624838656, i100 -267650600228229381612078366720, i200 1000000000000000019884624838656
// run: @wide(-1e38) -> returned i128 -99999999999999997748809823456034029568, i100 0, i200 -99999999999999997748809823456034029568
// run: @wide(1e300) -> returned i128 170141183460469231731687303715884105727, i100 -1, i200 803469022129495137770981046170581301261101496891396417650687
// run: @odd(3.0) -> returned i3 3, i3 3, i1 0, i1 1
// run: @odd(-4.0) -> returned i3 -4, i3 0, i1 1, i1 0
// run: @odd(4.0) -> returned i3 3, i3 -4, i1 0, i1 1
// f32 inputs: the largest f32 below 2^31, and 2^31.
// run: @f32s32(2147483520.0) -> returned i32 2147483520
// run: @f32s32(2147483648.0) -> trap convert
// run: @f32s32(-2147483648.0) -> returned i32 -2147483648
// int.to_float rounds to nearest, ties to even.
// run: @i2f(9007199254740993) -> returned f64 9007199254740992.0, f32 9007199000000000.0
// run: @i2f(9007199254740995) -> returned f64 9007199254740996.0, f32 9007199000000000.0
// run: @i2f(-9223372036854775808) -> returned f64 -9.223372036854776e18, f32 -9.223372e18
// run: @i2f(9223372036854775807) -> returned f64 9.223372036854776e18, f32 9.223372e18
// run: @i2f(16777217) -> returned f64 16777217.0, f32 16777216.0
// run: @i2f(-1) -> returned f64 -1.0, f32 -1.0
// run: @i2f(poison) -> returned f64 poison, f32 poison
// run: @u2f(-1) -> returned f64 1.8446744073709552e19, f32 1.8446744e19
// run: @u2f(9223372036854775808) -> returned f64 9.223372036854776e18, f32 9.223372e18
// run: @wide2f(-1) -> returned f64 -1.0, f32 -1.0, f64 3.2138760885179806e60
// run: @wide2f(1606938044258990275541962092341162602522202993782792835301376) -> returned f64 -1.6069380442589903e60, f32 -inf, f64 1.6069380442589903e60
// run: @wide2f(-1606938044258990275541962092341162602522202993782792835301375) -> returned f64 -1.6069380442589903e60, f32 -inf, f64 1.6069380442589903e60
// run: @i128f(170141183460469231731687303715884105727) -> returned f64 1.7014118346046923e38, f32 1.7014118e38, f32 1.7014118e38
// run: @i128f(-170141183460469231731687303715884105728) -> returned f64 -1.7014118346046923e38, f32 -1.7014118e38, f32 1.7014118e38
// run: @small(-1) -> returned f32 -1.0, f32 1.0, f64 -1.0
// float.ext is exact; float.trunc rounds, overflowing to infinity and underflowing to subnormals
// and zero.
// run: @ext(0.1) -> returned f64 0.10000000149011612
// run: @ext(1e-45) -> returned f64 1.401298464324817e-45
// run: @ext(-inf) -> returned f64 -inf
// run: @trunc(0.1) -> returned f32 0.1
// run: @trunc(3.4028235677973366e38) -> returned f32 inf
// run: @trunc(3.4028235677973362e38) -> returned f32 3.4028235e38
// run: @trunc(-1e39) -> returned f32 -inf
// run: @trunc(1e-46) -> returned f32 0.0
// run: @trunc(7.006492321624085e-46) -> returned f32 0.0
// run: @trunc(7.006492321624087e-46) -> returned f32 1e-45
// run: @trunc(2.1019476964872256e-45) -> returned f32 3e-45
// run: @trunc(1.1754942807573643e-38) -> returned f32 1.1754944e-38
// run: @trunc(-0.0) -> returned f32 -0.0
// run: @trunc(poison) -> returned f32 poison
func @s8(%x: f64) -> i8 {
  %r: i8 = float.to_int.s.sat %x
  func.ret %r
}

func @s8ub(%x: f64) -> i8 {
  %r: i8 = float.to_int.s.ub %x
  func.ret %r
}

func @s8trap(%x: f64) -> i8 {
  %r: i8 = float.to_int.s.trap %x
  func.ret %r
}

func @u8(%x: f32) -> i8 {
  %r: i8 = float.to_int.u.sat %x
  func.ret %r
}

func @u8trap(%x: f32) -> i8 {
  %r: i8 = float.to_int.u.trap %x
  func.ret %r
}

func @s64(%x: f64) -> (i64, i64) {
  %r: i64 = float.to_int.s.sat %x
  %t: i64 = float.to_int.s.trap %x
  func.ret %r, %t
}

func @u64(%x: f64) -> i64 {
  %r: i64 = float.to_int.u.sat %x
  func.ret %r
}

func @u64ub(%x: f64) -> i64 {
  %r: i64 = float.to_int.u.ub %x
  func.ret %r
}

func @wide(%x: f64) -> (i128, i100, i200) {
  %a: i128 = float.to_int.s.sat %x
  %b: i100 = float.to_int.u.sat %x
  %c: i200 = float.to_int.s.sat %x
  func.ret %a, %b, %c
}

func @odd(%x: f32) -> (i3, i3, i1, i1) {
  %a: i3 = float.to_int.s.sat %x
  %b: i3 = float.to_int.u.sat %x
  %c: i1 = float.to_int.s.sat %x
  %d: i1 = float.to_int.u.sat %x
  func.ret %a, %b, %c, %d
}

func @f32s32(%x: f32) -> i32 {
  %r: i32 = float.to_int.s.trap %x
  func.ret %r
}

func @i2f(%x: i64) -> (f64, f32) {
  %a: f64 = int.to_float.s %x
  %b: f32 = int.to_float.s %x
  func.ret %a, %b
}

func @u2f(%x: i64) -> (f64, f32) {
  %a: f64 = int.to_float.u %x
  %b: f32 = int.to_float.u %x
  func.ret %a, %b
}

func @wide2f(%x: i201) -> (f64, f32, f64) {
  %a: f64 = int.to_float.s %x
  %b: f32 = int.to_float.s %x
  %c: f64 = int.to_float.u %x
  func.ret %a, %b, %c
}

func @i128f(%x: i128) -> (f64, f32, f32) {
  %a: f64 = int.to_float.s %x
  %b: f32 = int.to_float.s %x
  %c: f32 = int.to_float.u %x
  func.ret %a, %b, %c
}

func @small(%x: i1) -> (f32, f32, f64) {
  %a: f32 = int.to_float.s %x
  %b: f32 = int.to_float.u %x
  %c: i5 = int.sext %x
  %d: f64 = int.to_float.s %c
  func.ret %a, %b, %d
}

func @ext(%x: f32) -> f64 {
  %r: f64 = float.ext %x
  func.ret %r
}

func @trunc(%x: f64) -> f32 {
  %r: f32 = float.trunc %x
  func.ret %r
}
