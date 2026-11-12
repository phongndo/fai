// Constants use the whole width: 2^127 is a valid i128 (signless), and prints signed.
// run: @top() -> returned i128 -170141183460469231731687303715884105728
// run: @max() -> returned i128 -1
func @top() -> i128 {
  %x: i128 = int.const 170141183460469231731687303715884105728
  func.ret %x
}

func @max() -> i128 {
  %x: i128 = int.const 340282366920938463463374607431768211455
  func.ret %x
}
