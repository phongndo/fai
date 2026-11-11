// run: @zext(-1) -> returned i32 255
// run: @sext(-1) -> returned i32 -1
// 300 is 0x12C; keeping the low 8 bits gives 0x2C = 44.
// run: @trunc_wrap(300) -> returned i8 44
// run: @trunc_nsw(300) -> returned i8 poison
// run: @trunc_nsw(-5) -> returned i8 -5
// 255 fits in 8 bits unsigned but not signed.
// run: @trunc_nuw(255) -> returned i8 -1
// run: @trunc_nsw(255) -> returned i8 poison
func @zext(%x: i8) -> i32 {
  %r: i32 = int.zext %x
  func.ret %r
}

func @sext(%x: i8) -> i32 {
  %r: i32 = int.sext %x
  func.ret %r
}

func @trunc_wrap(%x: i32) -> i8 {
  %r: i8 = int.trunc.wrap %x
  func.ret %r
}

func @trunc_nsw(%x: i32) -> i8 {
  %r: i8 = int.trunc.nsw %x
  func.ret %r
}

func @trunc_nuw(%x: i32) -> i8 {
  %r: i8 = int.trunc.nuw %x
  func.ret %r
}
