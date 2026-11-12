// error: in @f: @?: cf.yield: expected (i32) but got (i64)
func @f(%a: i64) -> i32 {
  %r: i32 = cf.try {
    cf.yield %a
  } catch(%e: ptr) {
    %z: i32 = int.const 0
    cf.yield %z
  }
  func.ret %r
}
